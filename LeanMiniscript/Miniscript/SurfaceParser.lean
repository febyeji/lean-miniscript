import LeanMiniscript.Miniscript.SurfacePretty
import LeanMiniscript.Miniscript.ValidationDecidable
import Init.Data.List.Lemmas
import Std.Data.String.ToNat

namespace LeanMiniscript.Miniscript

/-!
# Context-aware surface parser

Parsing is split into two boundaries:

1. a generic tokenizer and raw expression parser, which reports syntax and
   arity errors without knowing about keys; and
2. elaboration into `SurfaceFragment`, which resolves key tokens, decodes hash
   literals, and checks the selected P2WSH or Tapscript context.

Descriptor decoding and derivation remain outside this module. Callers provide
the key resolver used at the elaboration boundary.
-/

/-- Resolve one textual key token to public-key bytes. Context normalization
    happens after resolution, and the error string is preserved in
    `SurfaceParseError`. -/
abbrev KeyResolver := String → Except String PubKey

/-- Structured failures produced by the surface text boundary. -/
inductive SurfaceParseError where
  | emptyInput
  | unexpectedEnd (expected : String)
  | unexpectedToken (position : Nat) (expected found : String)
  | trailingInput (position : Nat) (found : String)
  | unknownFragment (position : Nat) (name : String)
  | unknownWrapper (position : Nat) (name : String)
  | invalidArity (position : Nat) (name expected : String) (actual : Nat)
  | expectedAtom (position : Nat) (role : String)
  | invalidNumber (position : Nat) (text : String)
  | invalidHex (position : Nat) (role text : String)
  | invalidHashLength (position : Nat) (role : String) (expected actual : Nat)
  | keyResolution (position : Nat) (token message : String)
  | keyContext (position : Nat) (token : String) (context : ScriptContext)
  | contextMismatch (position : Nat) (fragment : String) (context : ScriptContext)
  | validationFailed (context : ScriptContext)
  deriving Repr, DecidableEq, BEq, Inhabited

private inductive SurfaceTokenKind where
  | atom (value : String)
  | leftParen
  | rightParen
  | comma
  | colon
  deriving Repr

private structure SurfaceToken where
  kind : SurfaceTokenKind
  position : Nat
  deriving Repr

private inductive RawSurfaceExpr where
  | atom (position : Nat) (value : String)
  | wrapper (position : Nat) (name : String) (inner : RawSurfaceExpr)
  | call (position : Nat) (name : String) (arguments : List RawSurfaceExpr)
  deriving Repr, Inhabited

/-- Forget diagnostic positions after raw parsing. -/
private def RawSurfaceExpr.toExpr : RawSurfaceExpr → SurfaceText.Expr
  | .atom _ value => .atom value
  | .wrapper _ name inner => .wrapper name inner.toExpr
  | .call _ name arguments => .call name (arguments.map RawSurfaceExpr.toExpr)

private def finishTokenizedAtom (position : Nat) (reversed : List Char)
    (tail : List SurfaceToken) : List SurfaceToken :=
  match reversed with
  | [] => tail
  | _ =>
      ⟨.atom (String.ofList reversed.reverse), position⟩ :: tail

private def tokenizeChars (position atomPosition : Nat)
    (reversedAtom : List Char) : List Char → List SurfaceToken
  | [] => finishTokenizedAtom atomPosition reversedAtom []
  | char :: rest =>
      if SurfaceText.isSpace char then
        finishTokenizedAtom atomPosition reversedAtom
          (tokenizeChars (position + 1) (position + 1) [] rest)
      else
        match char with
        | '(' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.leftParen, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ')' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.rightParen, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ',' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.comma, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ':' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.colon, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | _ =>
            let start :=
              if reversedAtom.isEmpty then position else atomPosition
            tokenizeChars (position + 1) start (char :: reversedAtom) rest

private def tokenizeSurface (input : String) : List SurfaceToken :=
  tokenizeChars 0 0 [] input.toList

private def tokenText (token : SurfaceToken) : String :=
  match token.kind with
  | .atom value => value
  | .leftParen => "("
  | .rightParen => ")"
  | .comma => ","
  | .colon => ":"

/-- Forget source positions after tokenization. This is the bridge from the
    diagnostic lexer to the position-free canonical grammar used by proofs. -/
private def SurfaceToken.toLexeme (token : SurfaceToken) : SurfaceText.Lexeme :=
  match token.kind with
  | .atom value => .atom value
  | .leftParen => .leftParen
  | .rightParen => .rightParen
  | .comma => .comma
  | .colon => .colon

private def finishLexemeAtom (reversed : List Char)
    (tail : List SurfaceText.Lexeme) : List SurfaceText.Lexeme :=
  match reversed with
  | [] => tail
  | _ => .atom (String.ofList reversed.reverse) :: tail

private def tokenizeLexemeChars (reversedAtom : List Char) :
    List Char → List SurfaceText.Lexeme
  | [] => finishLexemeAtom reversedAtom []
  | char :: rest =>
      if SurfaceText.isSpace char then
        finishLexemeAtom reversedAtom (tokenizeLexemeChars [] rest)
      else
        match char with
        | '(' =>
            finishLexemeAtom reversedAtom
              (.leftParen :: tokenizeLexemeChars [] rest)
        | ')' =>
            finishLexemeAtom reversedAtom
              (.rightParen :: tokenizeLexemeChars [] rest)
        | ',' =>
            finishLexemeAtom reversedAtom
              (.comma :: tokenizeLexemeChars [] rest)
        | ':' =>
            finishLexemeAtom reversedAtom
              (.colon :: tokenizeLexemeChars [] rest)
        | _ => tokenizeLexemeChars (char :: reversedAtom) rest

private theorem tokenizeChars_toLexemes (position atomPosition : Nat)
    (reversedAtom chars : List Char) :
    (tokenizeChars position atomPosition reversedAtom chars).map
        SurfaceToken.toLexeme =
      tokenizeLexemeChars reversedAtom chars := by
  induction chars generalizing position atomPosition reversedAtom with
  | nil =>
      cases reversedAtom <;>
        simp [tokenizeChars, tokenizeLexemeChars, finishTokenizedAtom,
          finishLexemeAtom, SurfaceToken.toLexeme]
  | cons char rest ih =>
      simp only [tokenizeChars, tokenizeLexemeChars]
      split
      · cases reversedAtom <;>
          simp [finishTokenizedAtom, finishLexemeAtom,
            SurfaceToken.toLexeme, ih]
      · split <;> cases reversedAtom <;>
          simp [finishTokenizedAtom, finishLexemeAtom,
            SurfaceToken.toLexeme, ih]

private theorem tokenizeLexemeChars_safe_prefix
    (chars reversedAtom rest : List Char)
    (hSafe : ∀ char ∈ chars,
      SurfaceText.isSpace char = false ∧
        SurfaceText.isPunctuation char = false) :
    tokenizeLexemeChars reversedAtom (chars ++ rest) =
      tokenizeLexemeChars (chars.reverse ++ reversedAtom) rest := by
  induction chars generalizing reversedAtom with
  | nil => rfl
  | cons char chars ih =>
      have hChar := hSafe char (by simp)
      have hTail : ∀ tailChar ∈ chars,
          SurfaceText.isSpace tailChar = false ∧
            SurfaceText.isPunctuation tailChar = false := by
        intro tailChar hMem
        exact hSafe tailChar (by simp [hMem])
      simp only [List.cons_append, tokenizeLexemeChars]
      rw [if_neg (by simpa using hChar.1)]
      split <;> simp_all [SurfaceText.isPunctuation]

/-- Atoms must be nonempty, punctuation-free, and separated from one another
    for the diagnostic lexer to recover a canonical lexeme sequence exactly. -/
private def LexemesTokenizable : List SurfaceText.Lexeme → Prop
  | [] => True
  | .atom value :: [] => SurfaceText.AtomSafe value
  | .atom _ :: .atom _ :: _ => False
  | .atom value :: lexemes =>
      SurfaceText.AtomSafe value ∧ LexemesTokenizable lexemes
  | _ :: lexemes => LexemesTokenizable lexemes

private def SurfaceText.Lexeme.IsPunctuation : SurfaceText.Lexeme → Prop
  | .atom _ => False
  | _ => True

private theorem tokenizeLexemeChars_afterAtom_punctuation
    (value : String) (punctuation : SurfaceText.Lexeme)
    (rest : List Char) (hNonempty : value.toList ≠ [])
    (hPunctuation : punctuation.IsPunctuation) :
    tokenizeLexemeChars value.toList.reverse
        (punctuation.chars ++ rest) =
      .atom value :: tokenizeLexemeChars [] (punctuation.chars ++ rest) := by
  cases punctuation <;>
    simp_all [SurfaceText.Lexeme.IsPunctuation, SurfaceText.Lexeme.chars,
      tokenizeLexemeChars, finishLexemeAtom, SurfaceText.isSpace]

private theorem tokenizeLexemeChars_renderLexemes
    (lexemes : List SurfaceText.Lexeme)
    (hTokenizable : LexemesTokenizable lexemes) :
    tokenizeLexemeChars [] (lexemes.flatMap SurfaceText.Lexeme.chars) =
      lexemes := by
  induction lexemes with
  | nil => rfl
  | cons lexeme lexemes ih =>
      cases lexeme with
      | atom value =>
          cases lexemes with
          | nil =>
              have hSafe : SurfaceText.AtomSafe value := hTokenizable
              calc
                tokenizeLexemeChars []
                    ([SurfaceText.Lexeme.atom value].flatMap
                      SurfaceText.Lexeme.chars) =
                    tokenizeLexemeChars [] (value.toList ++ []) := by
                      simp [SurfaceText.Lexeme.chars]
                _ = tokenizeLexemeChars value.toList.reverse [] :=
                  by simpa using (tokenizeLexemeChars_safe_prefix
                    value.toList [] [] hSafe.2)
                _ = [SurfaceText.Lexeme.atom value] := by
                  simp [tokenizeLexemeChars, finishLexemeAtom, hSafe.1]
          | cons next rest =>
              have hNext : next.IsPunctuation := by
                cases next <;>
                  simp_all [LexemesTokenizable,
                    SurfaceText.Lexeme.IsPunctuation]
              have hSafe : SurfaceText.AtomSafe value := by
                cases next <;> simp_all [LexemesTokenizable]
              have hTail : LexemesTokenizable (next :: rest) := by
                cases next <;> simp_all [LexemesTokenizable]
              have ihTail := ih hTail
              calc
                tokenizeLexemeChars []
                    ((SurfaceText.Lexeme.atom value :: next :: rest).flatMap
                      SurfaceText.Lexeme.chars) =
                    tokenizeLexemeChars []
                      (value.toList ++
                        (next :: rest).flatMap SurfaceText.Lexeme.chars) := by
                          simp [SurfaceText.Lexeme.chars]
                _ = tokenizeLexemeChars value.toList.reverse
                      ((next :: rest).flatMap SurfaceText.Lexeme.chars) := by
                  simpa using (tokenizeLexemeChars_safe_prefix
                    value.toList []
                      ((next :: rest).flatMap SurfaceText.Lexeme.chars) hSafe.2)
                _ = SurfaceText.Lexeme.atom value ::
                      tokenizeLexemeChars []
                        ((next :: rest).flatMap SurfaceText.Lexeme.chars) := by
                  simpa using (tokenizeLexemeChars_afterAtom_punctuation
                    value next (rest.flatMap SurfaceText.Lexeme.chars)
                      hSafe.1 hNext)
                _ = SurfaceText.Lexeme.atom value :: next :: rest := by
                  rw [ihTail]
      | leftParen | rightParen | comma | colon =>
          have ihTail := ih hTokenizable
          simp [SurfaceText.Lexeme.chars, tokenizeLexemeChars,
            finishLexemeAtom, SurfaceText.isSpace, ihTail]

private theorem lexemesTokenizable_append_punctuation
    (lexemes : List SurfaceText.Lexeme) (punctuation : SurfaceText.Lexeme)
    (tail : List SurfaceText.Lexeme)
    (hLexemes : LexemesTokenizable lexemes)
    (hPunctuation : punctuation.IsPunctuation)
    (hTail : LexemesTokenizable tail) :
    LexemesTokenizable (lexemes ++ punctuation :: tail) := by
  induction lexemes with
  | nil =>
      cases punctuation <;>
        simp_all [LexemesTokenizable, SurfaceText.Lexeme.IsPunctuation]
  | cons lexeme lexemes ih =>
      cases lexeme <;> cases lexemes with
      | nil =>
          cases punctuation <;>
            simp_all [LexemesTokenizable, SurfaceText.Lexeme.IsPunctuation]
      | cons next rest =>
          cases next <;> cases punctuation <;>
            simp_all [LexemesTokenizable, SurfaceText.Lexeme.IsPunctuation]

mutual
  private theorem exprLexemesTokenizable (expr : SurfaceText.Expr)
      (hSafe : expr.AtomsSafe) : LexemesTokenizable expr.lexemes := by
    cases expr with
    | atom value =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe
        simpa [SurfaceText.Expr.lexemes, LexemesTokenizable] using hSafe
    | wrapper name inner =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe
        have hInner := exprLexemesTokenizable inner hSafe.2
        simpa [SurfaceText.Expr.lexemes, LexemesTokenizable] using
          And.intro hSafe.1 hInner
    | call name arguments =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe
        have hArguments := argumentLexemesTokenizable arguments hSafe.2
        have hClosed := lexemesTokenizable_append_punctuation
          (SurfaceText.argumentLexemes arguments) .rightParen []
            hArguments (by trivial) (by trivial)
        simpa [SurfaceText.Expr.lexemes, LexemesTokenizable] using
          And.intro hSafe.1 hClosed

  private theorem argumentLexemesTokenizable (arguments : List SurfaceText.Expr)
      (hSafe : ∀ argument ∈ arguments, argument.AtomsSafe) :
      LexemesTokenizable (SurfaceText.argumentLexemes arguments) := by
    cases arguments with
    | nil => trivial
    | cons argument arguments =>
        have hArgument := exprLexemesTokenizable argument
          (hSafe argument (by simp))
        cases arguments with
        | nil => simpa [SurfaceText.argumentLexemes] using hArgument
        | cons next rest =>
            have hRestSafe : ∀ restArgument ∈ next :: rest,
                restArgument.AtomsSafe := by
              intro restArgument hMem
              exact hSafe restArgument (by simp [hMem])
            have hRest := argumentLexemesTokenizable (next :: rest) hRestSafe
            simpa [SurfaceText.argumentLexemes] using
              lexemesTokenizable_append_punctuation
                argument.lexemes .comma
                  (SurfaceText.argumentLexemes (next :: rest))
                  hArgument (by trivial) hRest
end

private theorem tokenizeSurface_renderExpr (expr : SurfaceText.Expr)
    (hSafe : expr.AtomsSafe) :
    (tokenizeSurface expr.render).map SurfaceToken.toLexeme = expr.lexemes := by
  rw [tokenizeSurface, SurfaceText.Expr.render, String.toList_ofList]
  rw [tokenizeChars_toLexemes]
  exact tokenizeLexemeChars_renderLexemes expr.lexemes
    (exprLexemesTokenizable expr hSafe)

private abbrev RawParseResult :=
  Except SurfaceParseError (RawSurfaceExpr × List SurfaceToken)

private abbrev RawArgumentsResult :=
  Except SurfaceParseError (List RawSurfaceExpr × List SurfaceToken)

mutual
  private def parseRawFuel : Nat → List SurfaceToken → RawParseResult
    | 0, _ => .error (.unexpectedEnd "a fragment within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd "a Miniscript fragment")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .atom name =>
            match rest with
            | next :: remaining =>
                match next.kind with
                | .colon => do
                    let (inner, tail) ← parseRawFuel fuel remaining
                    pure (.wrapper token.position name inner, tail)
                | .leftParen => do
                    let (arguments, tail) ← parseRawArgumentsFuel fuel remaining
                    pure (.call token.position name arguments, tail)
                | _ => pure (.atom token.position name, rest)
            | [] => pure (.atom token.position name, [])
        | _ =>
            .error (.unexpectedToken token.position
              "a fragment name, wrapper, 0, or 1" (tokenText token))

  private def parseRawArgumentsFuel :
      Nat → List SurfaceToken → RawArgumentsResult
    | 0, _ => .error (.unexpectedEnd "arguments within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd "an argument or )")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .rightParen => pure ([], rest)
        | _ => do
            let (first, remaining) ← parseRawFuel fuel (token :: rest)
            parseMoreRawArgumentsFuel [first] fuel remaining

  private def parseMoreRawArgumentsFuel
      (reversed : List RawSurfaceExpr) :
      Nat → List SurfaceToken → RawArgumentsResult
    | 0, _ => .error (.unexpectedEnd "more arguments within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd ", or )")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .rightParen => pure (reversed.reverse, rest)
        | .comma => do
            let (next, remaining) ← parseRawFuel fuel rest
            parseMoreRawArgumentsFuel (next :: reversed) fuel remaining
        | _ =>
            .error (.unexpectedToken token.position ", or )" (tokenText token))
end

private def parseRaw (tokens : List SurfaceToken) : RawParseResult :=
  parseRawFuel (tokens.length + 1) tokens

private def remainingArgumentLexemes :
    List SurfaceText.Expr → List SurfaceText.Lexeme
  | [] => [.rightParen]
  | arguments@(_ :: _) =>
      .comma :: SurfaceText.argumentLexemes arguments ++ [.rightParen]

private theorem argumentLexemes_cons_append_rightParen
    (argument : SurfaceText.Expr) (arguments : List SurfaceText.Expr) :
    SurfaceText.argumentLexemes (argument :: arguments) ++ [.rightParen] =
      argument.lexemes ++ remainingArgumentLexemes arguments := by
  cases arguments <;> simp [SurfaceText.argumentLexemes,
    remainingArgumentLexemes]

private def StopsRawExpr : List SurfaceToken → Prop
  | [] => True
  | token :: _ =>
      token.toLexeme = .comma ∨ token.toLexeme = .rightParen

private theorem exists_split_of_map_eq_append
    {α β : Type} (mapValue : α → β) (values : List α)
    (left right : List β)
    (hMap : values.map mapValue = left ++ right) :
    ∃ leftValues rightValues,
      values = leftValues ++ rightValues ∧
        leftValues.map mapValue = left ∧
        rightValues.map mapValue = right := by
  induction left generalizing values with
  | nil =>
      exact ⟨[], values, by simp, rfl, by simpa using hMap⟩
  | cons value left ih =>
      cases values with
      | nil => simp at hMap
      | cons head values =>
          simp only [List.map_cons, List.cons_append] at hMap
          have hHead := congrArg List.head? hMap
          have hTail := congrArg List.tail hMap
          simp only [List.head?_cons] at hHead
          simp only [List.tail_cons] at hTail
          obtain ⟨leftValues, rightValues, hValues, hLeft, hRight⟩ :=
            ih values hTail
          have hHeadEq : mapValue head = value := Option.some.inj hHead
          exact ⟨head :: leftValues, rightValues, by simp [hValues],
            by simp [hHeadEq, hLeft], hRight⟩

private theorem stopsRawExpr_of_remainingArgumentLexemes
    (arguments : List SurfaceText.Expr) (tokens tail : List SurfaceToken)
    (hTokens : tokens.map SurfaceToken.toLexeme =
      remainingArgumentLexemes arguments) :
    StopsRawExpr (tokens ++ tail) := by
  cases arguments with
  | nil =>
      cases tokens with
      | nil => simp [remainingArgumentLexemes] at hTokens
      | cons token tokens =>
          simp [remainingArgumentLexemes, StopsRawExpr] at hTokens ⊢
          exact Or.inr hTokens.1
  | cons argument arguments =>
      cases tokens with
      | nil => simp [remainingArgumentLexemes] at hTokens
      | cons token tokens =>
          simp [remainingArgumentLexemes, StopsRawExpr] at hTokens ⊢
          exact Or.inl hTokens.1

private theorem tokenKind_eq_atom_of_toLexeme_eq
    (token : SurfaceToken) (value : String)
    (h : token.toLexeme = .atom value) : token.kind = .atom value := by
  rcases token with ⟨kind, position⟩
  cases kind <;> simp_all [SurfaceToken.toLexeme]

private theorem tokenKind_eq_leftParen_of_toLexeme_eq
    (token : SurfaceToken) (h : token.toLexeme = .leftParen) :
    token.kind = .leftParen := by
  rcases token with ⟨kind, position⟩
  cases kind <;> simp_all [SurfaceToken.toLexeme]

private theorem tokenKind_eq_rightParen_of_toLexeme_eq
    (token : SurfaceToken) (h : token.toLexeme = .rightParen) :
    token.kind = .rightParen := by
  rcases token with ⟨kind, position⟩
  cases kind <;> simp_all [SurfaceToken.toLexeme]

private theorem tokenKind_eq_comma_of_toLexeme_eq
    (token : SurfaceToken) (h : token.toLexeme = .comma) :
    token.kind = .comma := by
  rcases token with ⟨kind, position⟩
  cases kind <;> simp_all [SurfaceToken.toLexeme]

private theorem tokenKind_eq_colon_of_toLexeme_eq
    (token : SurfaceToken) (h : token.toLexeme = .colon) :
    token.kind = .colon := by
  rcases token with ⟨kind, position⟩
  cases kind <;> simp_all [SurfaceToken.toLexeme]

private def RawParserCorrect (fuel : Nat) : Prop :=
  (∀ (expr : SurfaceText.Expr) (tokens tail : List SurfaceToken),
    tokens.map SurfaceToken.toLexeme = expr.lexemes →
    StopsRawExpr tail →
    (tokens ++ tail).length < fuel →
    ∃ raw,
      parseRawFuel fuel (tokens ++ tail) = .ok (raw, tail) ∧
        raw.toExpr = expr) ∧
  (∀ (arguments : List SurfaceText.Expr) (tokens tail : List SurfaceToken),
    tokens.map SurfaceToken.toLexeme =
      SurfaceText.argumentLexemes arguments ++ [.rightParen] →
    (tokens ++ tail).length + 1 < fuel →
    ∃ raws,
      parseRawArgumentsFuel fuel (tokens ++ tail) = .ok (raws, tail) ∧
        raws.map RawSurfaceExpr.toExpr = arguments) ∧
  (∀ (reversed : List RawSurfaceExpr)
      (arguments : List SurfaceText.Expr) (tokens tail : List SurfaceToken),
    tokens.map SurfaceToken.toLexeme = remainingArgumentLexemes arguments →
    (tokens ++ tail).length + 1 < fuel →
    ∃ raws,
      parseMoreRawArgumentsFuel reversed fuel (tokens ++ tail) =
          .ok (raws, tail) ∧
        raws.map RawSurfaceExpr.toExpr =
          reversed.reverse.map RawSurfaceExpr.toExpr ++ arguments)

private theorem rawParserCorrect (fuel : Nat) : RawParserCorrect fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;>
        intro <;> intro <;> intro <;> intro <;> intro hFuel <;> omega
  | succ fuel ih =>
      obtain ⟨ihExpr, ihArguments, ihMore⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro expr tokens tail hTokens hStop hFuel
        cases expr with
        | atom value =>
            cases tokens with
            | nil => simp [SurfaceText.Expr.lexemes] at hTokens
            | cons token tokens =>
                cases tokens with
                | cons extra tokens =>
                    simp [SurfaceText.Expr.lexemes] at hTokens
                | nil =>
                    have hToken : token.toLexeme = .atom value := by
                      simpa [SurfaceText.Expr.lexemes] using hTokens
                    have hKind := tokenKind_eq_atom_of_toLexeme_eq
                      token value hToken
                    refine ⟨.atom token.position value, ?_, by
                      simp [RawSurfaceExpr.toExpr]⟩
                    cases tail with
                    | nil =>
                        simp [parseRawFuel, hKind]
                        rfl
                    | cons next rest =>
                        rcases hStop with hComma | hRightParen
                        · have hNext := tokenKind_eq_comma_of_toLexeme_eq
                            next hComma
                          simp [parseRawFuel, hKind, hNext]
                          rfl
                        · have hNext := tokenKind_eq_rightParen_of_toLexeme_eq
                            next hRightParen
                          simp [parseRawFuel, hKind, hNext]
                          rfl
        | wrapper name inner =>
            cases tokens with
            | nil => simp [SurfaceText.Expr.lexemes] at hTokens
            | cons nameToken tokens =>
                cases tokens with
                | nil => simp [SurfaceText.Expr.lexemes] at hTokens
                | cons colonToken innerTokens =>
                    simp only [List.map_cons, SurfaceText.Expr.lexemes] at hTokens
                    injection hTokens with hName hTokens
                    injection hTokens with hColon hInnerTokens
                    have hNameKind := tokenKind_eq_atom_of_toLexeme_eq
                      nameToken name hName
                    have hColonKind := tokenKind_eq_colon_of_toLexeme_eq
                      colonToken hColon
                    have hInnerFuel : (innerTokens ++ tail).length < fuel := by
                      simp only [List.length_cons, List.length_append] at hFuel ⊢
                      omega
                    obtain ⟨innerRaw, hParseInner, hInner⟩ :=
                      ihExpr inner innerTokens tail hInnerTokens hStop hInnerFuel
                    refine ⟨.wrapper nameToken.position name innerRaw, ?_, ?_⟩
                    · simp [parseRawFuel, hNameKind, hColonKind,
                        hParseInner] <;> rfl
                    · simp [RawSurfaceExpr.toExpr, hInner]
        | call name arguments =>
            cases tokens with
            | nil => simp [SurfaceText.Expr.lexemes] at hTokens
            | cons nameToken tokens =>
                cases tokens with
                | nil => simp [SurfaceText.Expr.lexemes] at hTokens
                | cons leftParenToken argumentTokens =>
                    simp only [List.map_cons, SurfaceText.Expr.lexemes] at hTokens
                    injection hTokens with hName hTokens
                    injection hTokens with hLeftParen hArgumentTokens
                    have hNameKind := tokenKind_eq_atom_of_toLexeme_eq
                      nameToken name hName
                    have hLeftParenKind :=
                      tokenKind_eq_leftParen_of_toLexeme_eq
                        leftParenToken hLeftParen
                    have hArgumentFuel :
                        (argumentTokens ++ tail).length + 1 < fuel := by
                      simpa using hFuel
                    obtain ⟨argumentRaws, hParseArguments, hArguments⟩ :=
                      ihArguments arguments argumentTokens tail
                        hArgumentTokens hArgumentFuel
                    refine ⟨.call nameToken.position name argumentRaws, ?_, ?_⟩
                    · simp [parseRawFuel, hNameKind, hLeftParenKind,
                        hParseArguments] <;> rfl
                    · simp [RawSurfaceExpr.toExpr, hArguments]
      · intro arguments tokens tail hTokens hFuel
        cases arguments with
        | nil =>
            cases tokens with
            | nil => simp [SurfaceText.argumentLexemes] at hTokens
            | cons token tokens =>
                cases tokens with
                | cons extra tokens =>
                    simp [SurfaceText.argumentLexemes] at hTokens
                | nil =>
                    have hToken : token.toLexeme = .rightParen := by
                      simpa [SurfaceText.argumentLexemes] using hTokens
                    have hKind := tokenKind_eq_rightParen_of_toLexeme_eq
                      token hToken
                    refine ⟨[], ?_, rfl⟩
                    simp [parseRawArgumentsFuel, hKind] <;> rfl
        | cons argument arguments =>
            rw [argumentLexemes_cons_append_rightParen] at hTokens
            obtain ⟨argumentTokens, remainingTokens, hSplit,
                hArgumentTokens, hRemainingTokens⟩ :=
              exists_split_of_map_eq_append SurfaceToken.toLexeme tokens
                argument.lexemes (remainingArgumentLexemes arguments) hTokens
            subst tokens
            have hStop := stopsRawExpr_of_remainingArgumentLexemes
              arguments remainingTokens tail hRemainingTokens
            have hExprFuel :
                (argumentTokens ++ (remainingTokens ++ tail)).length < fuel := by
              simpa [List.append_assoc] using hFuel
            obtain ⟨argumentRaw, hParseArgument, hArgument⟩ :=
              ihExpr argument argumentTokens (remainingTokens ++ tail)
                hArgumentTokens hStop hExprFuel
            have hArgumentTokensNonempty : argumentTokens ≠ [] := by
              intro hNil
              subst argumentTokens
              simp at hArgumentTokens
              exact argument.lexemes_ne_nil hArgumentTokens
            have hMoreFuel :
                (remainingTokens ++ tail).length + 1 < fuel := by
              simp only [List.length_append] at hFuel ⊢
              have : 0 < argumentTokens.length :=
                List.length_pos_iff.mpr hArgumentTokensNonempty
              omega
            obtain ⟨raws, hParseMore, hRaws⟩ :=
              ihMore [argumentRaw] arguments remainingTokens tail
                hRemainingTokens hMoreFuel
            obtain ⟨argumentToken, argumentTokenTail, hArgumentCons⟩ :=
              List.exists_cons_of_ne_nil hArgumentTokensNonempty
            subst argumentTokens
            obtain ⟨firstValue, firstTail, hFirst⟩ :=
              argument.lexemes_eq_atom_cons
            have hFirstToken : argumentToken.toLexeme = .atom firstValue := by
              simp only [List.map_cons] at hArgumentTokens
              rw [hFirst] at hArgumentTokens
              injection hArgumentTokens
            have hFirstKind := tokenKind_eq_atom_of_toLexeme_eq
              argumentToken firstValue hFirstToken
            refine ⟨raws, ?_, ?_⟩
            · simp only [Nat.add_one, List.append_assoc]
              change parseRawArgumentsFuel (Nat.succ fuel)
                  (argumentToken ::
                    (argumentTokenTail ++ (remainingTokens ++ tail))) =
                .ok (raws, tail)
              simp only [parseRawArgumentsFuel]
              rw [hFirstKind]
              have hParseArgument' :
                  parseRawFuel fuel
                      (argumentToken ::
                        (argumentTokenTail ++ (remainingTokens ++ tail))) =
                    .ok (argumentRaw, remainingTokens ++ tail) := by
                simpa using hParseArgument
              rw [hParseArgument']
              change parseMoreRawArgumentsFuel [argumentRaw] fuel
                  (remainingTokens ++ tail) = .ok (raws, tail)
              exact hParseMore
            · simpa [hArgument] using hRaws
      · intro reversed arguments tokens tail hTokens hFuel
        cases arguments with
        | nil =>
            cases tokens with
            | nil => simp [remainingArgumentLexemes] at hTokens
            | cons token tokens =>
                cases tokens with
                | cons extra tokens =>
                    simp [remainingArgumentLexemes] at hTokens
                | nil =>
                    have hToken : token.toLexeme = .rightParen := by
                      simpa [remainingArgumentLexemes] using hTokens
                    have hKind := tokenKind_eq_rightParen_of_toLexeme_eq
                      token hToken
                    refine ⟨reversed.reverse, ?_, by simp⟩
                    simp [parseMoreRawArgumentsFuel, hKind] <;> rfl
        | cons argument arguments =>
            cases tokens with
            | nil => simp [remainingArgumentLexemes] at hTokens
            | cons commaToken tokens =>
                simp only [List.map_cons, remainingArgumentLexemes] at hTokens
                injection hTokens with hComma hTokens
                have hTokens' := hTokens.trans
                  (argumentLexemes_cons_append_rightParen argument arguments)
                obtain ⟨argumentTokens, remainingTokens, hSplit,
                    hArgumentTokens, hRemainingTokens⟩ :=
                  exists_split_of_map_eq_append SurfaceToken.toLexeme tokens
                    argument.lexemes (remainingArgumentLexemes arguments) hTokens'
                subst tokens
                have hCommaKind := tokenKind_eq_comma_of_toLexeme_eq
                  commaToken hComma
                have hStop := stopsRawExpr_of_remainingArgumentLexemes
                  arguments remainingTokens tail hRemainingTokens
                have hExprFuel :
                    (argumentTokens ++ (remainingTokens ++ tail)).length < fuel := by
                  simp only [List.length_cons, List.length_append] at hFuel ⊢
                  omega
                obtain ⟨argumentRaw, hParseArgument, hArgument⟩ :=
                  ihExpr argument argumentTokens (remainingTokens ++ tail)
                    hArgumentTokens hStop hExprFuel
                have hArgumentTokensNonempty : argumentTokens ≠ [] := by
                  intro hNil
                  subst argumentTokens
                  simp at hArgumentTokens
                  exact argument.lexemes_ne_nil hArgumentTokens
                have hMoreFuel :
                    (remainingTokens ++ tail).length + 1 < fuel := by
                  simp only [List.length_cons, List.length_append] at hFuel ⊢
                  have : 0 < argumentTokens.length :=
                    List.length_pos_iff.mpr hArgumentTokensNonempty
                  omega
                obtain ⟨raws, hParseMore, hRaws⟩ :=
                  ihMore (argumentRaw :: reversed) arguments
                    remainingTokens tail hRemainingTokens hMoreFuel
                refine ⟨raws, ?_, ?_⟩
                · simp only [Nat.add_one]
                  rw [show
                    (commaToken :: (argumentTokens ++ remainingTokens)) ++ tail =
                      commaToken ::
                        (argumentTokens ++ (remainingTokens ++ tail)) by
                    simp [List.append_assoc]]
                  change parseMoreRawArgumentsFuel reversed (Nat.succ fuel)
                      (commaToken ::
                        (argumentTokens ++ (remainingTokens ++ tail))) =
                    .ok (raws, tail)
                  simp only [parseMoreRawArgumentsFuel]
                  rw [hCommaKind]
                  rw [hParseArgument]
                  change parseMoreRawArgumentsFuel (argumentRaw :: reversed)
                      fuel (remainingTokens ++ tail) = .ok (raws, tail)
                  exact hParseMore
                · simpa [hArgument, List.reverse_cons, List.append_assoc] using
                    hRaws

private theorem parseRaw_tokenizeSurface_renderExpr
    (expr : SurfaceText.Expr) (hSafe : expr.AtomsSafe) :
    ∃ raw,
      parseRaw (tokenizeSurface expr.render) = .ok (raw, []) ∧
        raw.toExpr = expr := by
  let tokens := tokenizeSurface expr.render
  have hTokens : tokens.map SurfaceToken.toLexeme = expr.lexemes := by
    exact tokenizeSurface_renderExpr expr hSafe
  obtain ⟨raw, hParse, hRaw⟩ :=
    (rawParserCorrect (tokens.length + 1)).1 expr tokens []
      hTokens (by trivial) (by simp)
  exact ⟨raw, by simpa [parseRaw] using hParse, hRaw⟩

private def unaryArgument (position : Nat) (name : String) :
    List RawSurfaceExpr → Except SurfaceParseError RawSurfaceExpr
  | [argument] => pure argument
  | arguments =>
      .error (.invalidArity position name "exactly 1 argument" arguments.length)

private def binaryArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × RawSurfaceExpr)
  | [x, y] => pure (x, y)
  | arguments =>
      .error (.invalidArity position name "exactly 2 arguments" arguments.length)

private def ternaryArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × RawSurfaceExpr × RawSurfaceExpr)
  | [x, y, z] => pure (x, y, z)
  | arguments =>
      .error (.invalidArity position name "exactly 3 arguments" arguments.length)

private def variadicArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × List RawSurfaceExpr)
  | first :: rest =>
      if rest.isEmpty then
        .error (.invalidArity position name
          "a threshold and at least 1 item" 1)
      else
        pure (first, rest)
  | [] =>
      .error (.invalidArity position name
        "a threshold and at least 1 item" 0)

private def rawAtom (role : String) :
    RawSurfaceExpr → Except SurfaceParseError (Nat × String)
  | .atom position value => pure (position, value)
  | .wrapper position _ _ | .call position _ _ =>
      .error (.expectedAtom position role)

private def parseNatRaw (role : String)
    (raw : RawSurfaceExpr) : Except SurfaceParseError Nat := do
  let (position, text) ← rawAtom role raw
  match text.toNat? with
  | some value => pure value
  | none => .error (.invalidNumber position text)

private def hexNibble? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' | 'A' => some 10
  | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12
  | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14
  | 'f' | 'F' => some 15
  | _ => none

private def decodeHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let highValue ← hexNibble? high
      let lowValue ← hexNibble? low
      let tail ← decodeHexChars? rest
      pure (UInt8.ofNat (highValue * 16 + lowValue) :: tail)
  | [_] => none

private def decodeHex? (text : String) : Option ByteArray := do
  let bytes ← decodeHexChars? text.toList
  pure ⟨bytes.toArray⟩

private theorem hexNibble_hexDigit (n : Nat) (h : n < 16) :
    hexNibble? (LeanMiniscript.Script.hexDigit n) = some n := by
  have hAll : ∀ value : Fin 16,
      hexNibble? (LeanMiniscript.Script.hexDigit value.val) =
        some value.val := by
    decide
  exact hAll ⟨n, h⟩

private theorem byteHexValueUInt8 (byte : UInt8) :
    UInt8.ofNat (byte.toNat / 16) * 16 +
        UInt8.ofNat (byte.toNat % 16) = byte := by
  have hAll : ∀ value : Fin 256,
      UInt8.ofNat ((UInt8.ofNat value.val).toNat / 16) * 16 +
          UInt8.ofNat ((UInt8.ofNat value.val).toNat % 16) =
        UInt8.ofNat value.val := by
    set_option maxRecDepth 100000 in
      decide
  simpa using hAll ⟨byte.toNat, byte.toNat_lt⟩

private theorem decodeHexChars_byteHexChars_append
    (byte : UInt8) (chars : List Char) :
    decodeHexChars?
        (LeanMiniscript.Script.byteHexChars byte ++ chars) =
      match decodeHexChars? chars with
      | some tail => some (byte :: tail)
      | none => none := by
  have hHigh : byte.toNat / 16 < 16 := by
    have := byte.toNat_lt
    omega
  have hLow : byte.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
  simp [LeanMiniscript.Script.byteHexChars, decodeHexChars?,
    hexNibble_hexDigit, hHigh, hLow]
  rw [byteHexValueUInt8]
  cases decodeHexChars? chars <;> rfl

private theorem decodeHexChars_byteHexChars (bytes : List UInt8) :
    decodeHexChars?
        (bytes.flatMap LeanMiniscript.Script.byteHexChars) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      rw [List.flatMap_cons, decodeHexChars_byteHexChars_append, ih]

private theorem decodeHex_byteArrayHex (bytes : ByteArray) :
    decodeHex? (LeanMiniscript.Script.byteArrayHex bytes) = some bytes := by
  rcases bytes with ⟨data⟩
  simp [decodeHex?, LeanMiniscript.Script.byteArrayHex,
    decodeHexChars_byteHexChars]

private theorem parseNatRaw_toString
    (role : String) (position value : Nat) :
    parseNatRaw role (.atom position (toString value)) = .ok value := by
  simp [parseNatRaw, rawAtom, Nat.toNat?_repr]
  rfl

private theorem parseNatRaw_repr
    (role : String) (position value : Nat) :
    parseNatRaw role (.atom position value.repr) = .ok value := by
  simp [parseNatRaw, rawAtom, Nat.toNat?_repr]
  rfl

private theorem atomCharSafe_of_digit_or_underscore (char : Char)
    (h : char.isDigit ∨ char = '_') :
    SurfaceText.isSpace char = false ∧
      SurfaceText.isPunctuation char = false := by
  rcases h with hDigit | rfl
  · have hBounds := Char.isDigit_iff_toNat.mp hDigit
    constructor
    · unfold SurfaceText.isSpace
      split <;> simp_all <;> omega
    · unfold SurfaceText.isPunctuation
      split <;> simp_all <;> omega
  · decide

private theorem atomSafe_toString (value : Nat) :
    SurfaceText.AtomSafe (toString value) := by
  have hNat := String.isNat_iff.mp (Nat.isNat_repr value)
  constructor
  · change value.repr.toList ≠ []
    intro hEmpty
    exact hNat.1 (String.toList_eq_nil_iff.mp hEmpty)
  · intro char hMem
    exact atomCharSafe_of_digit_or_underscore char (hNat.2.1 char hMem)

private theorem byteHexChars_atomCharsSafe (byte : UInt8) :
    ∀ char ∈ LeanMiniscript.Script.byteHexChars byte,
      SurfaceText.isSpace char = false ∧
        SurfaceText.isPunctuation char = false := by
  have hAll : ∀ value : Fin 256,
      ∀ char ∈ LeanMiniscript.Script.byteHexChars (UInt8.ofNat value.val),
        SurfaceText.isSpace char = false ∧
          SurfaceText.isPunctuation char = false := by
    set_option maxRecDepth 100000 in
      decide
  simpa using hAll ⟨byte.toNat, byte.toNat_lt⟩

private theorem atomSafe_byteArrayHex (bytes : ByteArray)
    (hPositive : 0 < bytes.size) :
    SurfaceText.AtomSafe (LeanMiniscript.Script.byteArrayHex bytes) := by
  unfold SurfaceText.AtomSafe LeanMiniscript.Script.byteArrayHex
  simp only [String.toList_ofList]
  constructor
  · intro hEmpty
    have hData : bytes.data.toList ≠ [] := by
      intro hDataEmpty
      have hLength : bytes.data.toList.length = [].length :=
        congrArg List.length hDataEmpty
      have hSizeZero : bytes.size = 0 := by
        change bytes.data.size = 0
        simpa only [Array.length_toList, List.length_nil] using hLength
      omega
    cases hBytes : bytes.data.toList with
    | nil => exact hData hBytes
    | cons byte tail =>
        simp [hBytes, LeanMiniscript.Script.byteHexChars] at hEmpty
  · intro char hMem
    simp only [List.mem_flatMap] at hMem
    obtain ⟨byte, _, hChar⟩ := hMem
    exact byteHexChars_atomCharsSafe byte char hChar

/-- Default key resolver for canonical lowercase or uppercase hexadecimal key
    tokens. Context-specific length checks remain in `parseSurface`. -/
def resolveHexKey (token : String) : Except String PubKey :=
  match decodeHex? token with
  | some bytes => pure (PubKey.ofBytes bytes)
  | none => .error "expected an even-length hexadecimal public key"

private def parseHashBytes (role : String) (expectedLength : Nat)
    (raw : RawSurfaceExpr) : Except SurfaceParseError ByteArray := do
  let (position, text) ← rawAtom role raw
  match decodeHex? text with
  | none => .error (.invalidHex position role text)
  | some bytes =>
      if bytes.size = expectedLength then
        pure bytes
      else
        .error (.invalidHashLength position role expectedLength bytes.size)

/-- Normalize resolved key bytes to the representation embedded in Script.
    BIP 386 permits compressed key expressions under `tr()`, but their
    33-byte serialization must become a 32-byte x-only Tapscript key. -/
private def normalizeKeyForContext
    (context : ScriptContext) (key : PubKey) : Option PubKey :=
  match context with
  | .p2wsh =>
      if key.size = 33 then some key else none
  | .tapscript =>
      if key.size = 32 then
        some key
      else if key.size = 33 then
        let keyPrefix := key.bytes.get! 0
        if keyPrefix = 0x02 || keyPrefix = 0x03 then
          some (PubKey.ofBytes (key.bytes.extract 1 33))
        else
          none
      else
        none

private def resolveKeyRaw (context : ScriptContext) (resolver : KeyResolver)
    (raw : RawSurfaceExpr) : Except SurfaceParseError PubKey := do
  let (position, token) ← rawAtom "a key token" raw
  match resolver token with
  | .error message => .error (.keyResolution position token message)
  | .ok key =>
      match normalizeKeyForContext context key with
      | some normalized => pure normalized
      | none => .error (.keyContext position token context)

private theorem resolveHexKey_prettyPubKey (key : PubKey) :
    resolveHexKey (prettyPubKey key) = .ok key := by
  simp [resolveHexKey, prettyPubKey, decodeHex_byteArrayHex,
    PubKey.ofBytes]
  rfl

private theorem normalizeKeyForContext_of_valid
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    normalizeKeyForContext context key = some key := by
  cases context <;>
    simp_all [normalizeKeyForContext, validResolvedPubKey]

private theorem resolveKeyRaw_prettyPubKey
    (context : ScriptContext) (position : Nat) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    resolveKeyRaw context resolveHexKey
        (.atom position (prettyPubKey key)) = .ok key := by
  simp [resolveKeyRaw, rawAtom, resolveHexKey_prettyPubKey,
    normalizeKeyForContext_of_valid context key hValid]
  rfl

private theorem parseHashBytes_byteArrayHex
    (role : String) (expectedLength position : Nat) (bytes : ByteArray)
    (hSize : bytes.size = expectedLength) :
    parseHashBytes role expectedLength
        (.atom position (LeanMiniscript.Script.byteArrayHex bytes)) =
      .ok bytes := by
  simp [parseHashBytes, rawAtom, decodeHex_byteArrayHex, hSize]
  rfl

private def validateSurface (context : ScriptContext)
    (fragment : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  if _ : fragment.WellFormed context then
    pure fragment
  else
    .error (.validationFailed context)

private def applyWrapper (position : Nat) (wrapper : Char)
    (fragment : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  match wrapper with
  | 'a' => pure (.core (.a (desugar fragment)))
  | 's' => pure (.core (.s (desugar fragment)))
  | 'c' => pure (.core (.c (desugar fragment)))
  | 'd' => pure (.core (.d (desugar fragment)))
  | 'v' => pure (.core (.v (desugar fragment)))
  | 'j' => pure (.core (.j (desugar fragment)))
  | 'n' => pure (.core (.n (desugar fragment)))
  | 't' => pure (.t fragment)
  | 'l' => pure (.l fragment)
  | 'u' => pure (.u fragment)
  | unknown =>
      .error (.unknownWrapper position (String.ofList [unknown]))

private def applyWrapperChain (position : Nat) (name : String)
    (inner : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  name.toList.foldrM (applyWrapper position) inner

private def CanonicalWrapper (wrapper : Char) : Prop :=
  wrapper = 'a' ∨ wrapper = 's' ∨ wrapper = 'c' ∨ wrapper = 'd' ∨
    wrapper = 'v' ∨ wrapper = 'j' ∨ wrapper = 'n' ∨ wrapper = 't' ∨
    wrapper = 'l' ∨ wrapper = 'u'

private def CanonicalWrappers (name : String) : Prop :=
  ∀ wrapper ∈ name.toList, CanonicalWrapper wrapper

private def wrapSurface : Char → SurfaceFragment → SurfaceFragment
  | 'a', fragment => .core (.a (desugar fragment))
  | 's', fragment => .core (.s (desugar fragment))
  | 'c', fragment => .core (.c (desugar fragment))
  | 'd', fragment => .core (.d (desugar fragment))
  | 'v', fragment => .core (.v (desugar fragment))
  | 'j', fragment => .core (.j (desugar fragment))
  | 'n', fragment => .core (.n (desugar fragment))
  | 't', fragment => .t fragment
  | 'l', fragment => .l fragment
  | 'u', fragment => .u fragment
  | _, fragment => fragment

private def wrapSurfaceChain (name : String)
    (inner : SurfaceFragment) : SurfaceFragment :=
  name.toList.foldr wrapSurface inner

private theorem applyWrapper_of_canonical
    (position : Nat) (wrapper : Char) (inner : SurfaceFragment)
    (hCanonical : CanonicalWrapper wrapper) :
    applyWrapper position wrapper inner = .ok (wrapSurface wrapper inner) := by
  rcases hCanonical with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

private theorem applyWrapperChain_of_canonical
    (position : Nat) (name : String) (inner : SurfaceFragment)
    (hCanonical : CanonicalWrappers name) :
    applyWrapperChain position name inner =
      .ok (wrapSurfaceChain name inner) := by
  unfold applyWrapperChain wrapSurfaceChain CanonicalWrappers at *
  generalize name.toList = wrappers at hCanonical ⊢
  induction wrappers with
  | nil => rfl
  | cons wrapper wrappers ih =>
      have hWrapper := hCanonical wrapper (by simp)
      have hWrappers : ∀ candidate ∈ wrappers,
          CanonicalWrapper candidate := by
        intro candidate hMem
        exact hCanonical candidate (by simp [hMem])
      rw [List.foldrM_cons, ih hWrappers]
      exact applyWrapper_of_canonical position wrapper _ hWrapper

private theorem wrapSurfaceChain_append
    (first second : String) (inner : SurfaceFragment) :
    wrapSurfaceChain (first ++ second) inner =
      wrapSurfaceChain first (wrapSurfaceChain second inner) := by
  simp [wrapSurfaceChain, String.toList_append, List.foldr_append]

private theorem canonicalWrappers_append_char
    (wrappers : String) (wrapper : Char)
    (hWrappers : CanonicalWrappers wrappers)
    (hWrapper : CanonicalWrapper wrapper) :
    CanonicalWrappers (wrappers ++ String.ofList [wrapper]) := by
  intro candidate hMem
  simp only [String.toList_append, String.toList_ofList,
    List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hMem | rfl
  · exact hWrappers candidate hMem
  · exact hWrapper

private theorem canonicalWrapper_atomCharSafe (wrapper : Char)
    (hCanonical : CanonicalWrapper wrapper) :
    SurfaceText.isSpace wrapper = false ∧
      SurfaceText.isPunctuation wrapper = false := by
  rcases hCanonical with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> decide

private theorem atomSafe_of_canonicalWrappers
    (wrappers : String) (hNonempty : wrappers ≠ "")
    (hCanonical : CanonicalWrappers wrappers) :
    SurfaceText.AtomSafe wrappers := by
  constructor
  · simpa using hNonempty
  · intro wrapper hMem
    exact canonicalWrapper_atomCharSafe wrapper
      (hCanonical wrapper hMem)

private def elaborateRawFuel (context : ScriptContext)
    (resolver : KeyResolver) :
      Nat → RawSurfaceExpr → Except SurfaceParseError SurfaceFragment
  | 0, _ =>
      .error (.unexpectedEnd "a fragment within the elaboration budget")
  | _ + 1, .atom position value =>
      if value = "0" then
        pure (.core .zero)
      else if value = "1" then
        pure (.core .one)
      else
        .error (.unknownFragment position value)
  | fuel + 1, .wrapper position name inner => do
      let fragment ← elaborateRawFuel context resolver fuel inner
      applyWrapperChain position name fragment
  | fuel + 1, .call position name arguments => do
      if name = "pk" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.pk key)
      else if name = "pkh" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.pkh key)
      else if name = "pk_k" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.core (.pk_k key))
      else if name = "pk_h" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.core (.pk_h key))
      else if name = "older" then
        let argument ← unaryArgument position name arguments
        pure (.core (.older (← parseNatRaw "a relative timelock" argument)))
      else if name = "after" then
        let argument ← unaryArgument position name arguments
        pure (.core (.after (← parseNatRaw "an absolute timelock" argument)))
      else if name = "sha256" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "sha256" 32 argument
        pure (.core (.sha256 (Hash256.ofBytes bytes)))
      else if name = "hash256" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "hash256" 32 argument
        pure (.core (.hash256 (Hash256.ofBytes bytes)))
      else if name = "ripemd160" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "ripemd160" 20 argument
        pure (.core (.ripemd160 (Hash160.ofBytes bytes)))
      else if name = "hash160" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "hash160" 20 argument
        pure (.core (.hash160 (Hash160.ofBytes bytes)))
      else if name = "and_n" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.and_n x y)
      else if name = "and_v" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.and_v (desugar x) (desugar y)))
      else if name = "and_b" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.and_b (desugar x) (desugar y)))
      else if name = "or_b" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_b (desugar x) (desugar y)))
      else if name = "or_c" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_c (desugar x) (desugar y)))
      else if name = "or_d" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_d (desugar x) (desugar y)))
      else if name = "or_i" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_i (desugar x) (desugar y)))
      else if name = "andor" then
        let (xRaw, yRaw, zRaw) ← ternaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        let z ← elaborateRawFuel context resolver fuel zRaw
        pure (.core (.andor (desugar x) (desugar y) (desugar z)))
      else if name = "thresh" then
        let (thresholdRaw, fragmentRaws) ←
          variadicArguments position name arguments
        let threshold ← parseNatRaw "a threshold" thresholdRaw
        let fragments ←
          fragmentRaws.mapM (elaborateRawFuel context resolver fuel)
        pure (.core (.thresh threshold (fragments.map desugar)))
      else if name = "multi" then
        let (thresholdRaw, keyRaws) ←
          variadicArguments position name arguments
        match context with
        | .tapscript =>
            .error (.contextMismatch position name context)
        | .p2wsh =>
            let threshold ← parseNatRaw "a threshold" thresholdRaw
            let keys ← keyRaws.mapM (resolveKeyRaw context resolver)
            pure (.core (.multi threshold keys))
      else if name = "multi_a" then
        let (thresholdRaw, keyRaws) ←
          variadicArguments position name arguments
        match context with
        | .p2wsh =>
            .error (.contextMismatch position name context)
        | .tapscript =>
            let threshold ← parseNatRaw "a threshold" thresholdRaw
            let keys ← keyRaws.mapM (resolveKeyRaw context resolver)
            pure (.core (.multi_a threshold keys))
      else
        .error (.unknownFragment position name)

private def CanonicalExprElaborates (context : ScriptContext)
    (expr : SurfaceText.Expr) (fragment : SurfaceFragment) : Prop :=
  ∀ (fuel : Nat) (raw : RawSurfaceExpr),
    raw.toExpr = expr → expr.lexemes.length < fuel →
      elaborateRawFuel context resolveHexKey fuel raw = .ok fragment

private def CanonicalExprCorrect (context : ScriptContext)
    (expr : SurfaceText.Expr) (fragment : SurfaceFragment) : Prop :=
  expr.AtomsSafe ∧ CanonicalExprElaborates context expr fragment

private theorem canonicalExprCorrect_prependWrappers
    (context : ScriptContext) (wrappers : String)
    (body : SurfaceText.Expr) (fragment : SurfaceFragment)
    (hWrappers : CanonicalWrappers wrappers)
    (hBody : CanonicalExprCorrect context body fragment) :
    CanonicalExprCorrect context
      (SurfaceText.prependWrappers wrappers body)
      (wrapSurfaceChain wrappers fragment) := by
  constructor
  · by_cases hEmpty : wrappers.isEmpty
    · have hWrappersEmpty : wrappers = "" := String.isEmpty_iff.mp hEmpty
      subst wrappers
      simpa [SurfaceText.prependWrappers] using hBody.1
    · have hNonempty : wrappers ≠ "" := by
        intro hWrappersEmpty
        subst wrappers
        simp at hEmpty
      rw [SurfaceText.prependWrappers, if_neg hEmpty]
      unfold SurfaceText.Expr.AtomsSafe
      exact ⟨atomSafe_of_canonicalWrappers wrappers hNonempty hWrappers,
        hBody.1⟩
  · intro fuel raw hRaw hFuel
    by_cases hEmpty : wrappers.isEmpty
    · have hWrappersEmpty : wrappers = "" := String.isEmpty_iff.mp hEmpty
      subst wrappers
      simpa [SurfaceText.prependWrappers, wrapSurfaceChain] using
        hBody.2 fuel raw (by
          simpa [SurfaceText.prependWrappers] using hRaw) (by
          simpa [SurfaceText.prependWrappers] using hFuel)
    · cases raw with
      | atom position value =>
          simp [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers, hEmpty]
            at hRaw
      | call position name arguments =>
          simp [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers, hEmpty]
            at hRaw
      | wrapper position name inner =>
          simp only [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers,
            hEmpty] at hRaw
          cases hRaw
          cases fuel with
          | zero =>
              simp at hFuel
          | succ fuel =>
              have hInnerFuel :
                  (SurfaceText.Expr.lexemes inner.toExpr).length < fuel := by
                simp [SurfaceText.prependWrappers, hEmpty,
                  SurfaceText.Expr.lexemes] at hFuel
                omega
              simp only [elaborateRawFuel]
              rw [hBody.2 fuel inner rfl hInnerFuel]
              exact applyWrapperChain_of_canonical position wrappers fragment
                hWrappers

private theorem canonicalExprCorrect_atom
    (context : ScriptContext) (value : String) (fragment : SurfaceFragment)
    (hSafe : SurfaceText.AtomSafe value)
    (hElaborate : ∀ (fuel position : Nat),
      (SurfaceText.Expr.atom value).lexemes.length < fuel →
        elaborateRawFuel context resolveHexKey fuel (.atom position value) =
          .ok fragment) :
    CanonicalExprCorrect context (.atom value) fragment := by
  constructor
  · unfold SurfaceText.Expr.AtomsSafe
    exact hSafe
  · intro fuel raw hRaw hFuel
    cases raw with
    | atom position rawValue =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel position hFuel
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call => simp [RawSurfaceExpr.toExpr] at hRaw

private theorem canonicalExprCorrect_call
    (context : ScriptContext) (name : String)
    (arguments : List SurfaceText.Expr) (fragment : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hArgumentsSafe : ∀ argument ∈ arguments, argument.AtomsSafe)
    (hElaborate : ∀ (fuel position : Nat)
      (rawArguments : List RawSurfaceExpr),
      rawArguments.map RawSurfaceExpr.toExpr = arguments →
      (SurfaceText.Expr.call name arguments).lexemes.length < fuel →
        elaborateRawFuel context resolveHexKey fuel
          (.call position name rawArguments) = .ok fragment) :
    CanonicalExprCorrect context (.call name arguments) fragment := by
  constructor
  · unfold SurfaceText.Expr.AtomsSafe
    exact ⟨hNameSafe, hArgumentsSafe⟩
  · intro fuel raw hRaw hFuel
    cases raw with
    | atom => simp [RawSurfaceExpr.toExpr] at hRaw
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call position rawName rawArguments =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel position rawArguments rfl hFuel

private theorem rawExprMap_eq_cons
    (raws : List RawSurfaceExpr) (expr : SurfaceText.Expr)
    (exprs : List SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = expr :: exprs) :
    ∃ raw rest, raws = raw :: rest ∧ raw.toExpr = expr ∧
      rest.map RawSurfaceExpr.toExpr = exprs := by
  cases raws with
  | nil => simp at hMap
  | cons raw rest =>
      simp only [List.map_cons, List.cons.injEq] at hMap
      exact ⟨raw, rest, rfl, hMap.1, hMap.2⟩

private theorem rawExprMap_eq_nil (raws : List RawSurfaceExpr)
    (hMap : raws.map RawSurfaceExpr.toExpr = []) : raws = [] := by
  cases raws <;> simp_all

private theorem rawExprMap_eq_singleton
    (raws : List RawSurfaceExpr) (expr : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [expr]) :
    ∃ raw, raws = [raw] ∧ raw.toExpr = expr := by
  obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
    rawExprMap_eq_cons raws expr [] hMap
  have : rest = [] := rawExprMap_eq_nil rest hRest
  subst rest
  exact ⟨raw, rfl, hRaw⟩

private theorem rawExprMap_eq_pair
    (raws : List RawSurfaceExpr) (first second : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [first, second]) :
    ∃ firstRaw secondRaw,
      raws = [firstRaw, secondRaw] ∧
        firstRaw.toExpr = first ∧ secondRaw.toExpr = second := by
  obtain ⟨firstRaw, rest, rfl, hFirst, hRest⟩ :=
    rawExprMap_eq_cons raws first [second] hMap
  obtain ⟨secondRaw, hRest, hSecond⟩ :=
    rawExprMap_eq_singleton rest second hRest
  subst rest
  exact ⟨firstRaw, secondRaw, rfl, hFirst, hSecond⟩

private theorem rawExprMap_eq_triple
    (raws : List RawSurfaceExpr) (first second third : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [first, second, third]) :
    ∃ firstRaw secondRaw thirdRaw,
      raws = [firstRaw, secondRaw, thirdRaw] ∧
        firstRaw.toExpr = first ∧ secondRaw.toExpr = second ∧
          thirdRaw.toExpr = third := by
  obtain ⟨firstRaw, rest, rfl, hFirst, hRest⟩ :=
    rawExprMap_eq_cons raws first [second, third] hMap
  obtain ⟨secondRaw, thirdRaw, hRest, hSecond, hThird⟩ :=
    rawExprMap_eq_pair rest second third hRest
  subst rest
  exact ⟨firstRaw, secondRaw, thirdRaw, rfl, hFirst, hSecond, hThird⟩

private theorem canonicalWrappers_empty : CanonicalWrappers "" := by
  intro wrapper hMem
  simp at hMem

private theorem canonicalExprCorrect_zero (context : ScriptContext) :
    CanonicalExprCorrect context (.atom "0") (.core .zero) := by
  apply canonicalExprCorrect_atom
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel position hFuel
    cases fuel with
    | zero => simp at hFuel
    | succ fuel => simp [elaborateRawFuel]; rfl

private theorem canonicalExprCorrect_one (context : ScriptContext) :
    CanonicalExprCorrect context (.atom "1") (.core .one) := by
  apply canonicalExprCorrect_atom
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel position hFuel
    cases fuel with
    | zero => simp at hFuel
    | succ fuel => simp [elaborateRawFuel]; rfl

private theorem canonicalExprCorrect_unaryAtomCall
    (context : ScriptContext) (name token : String)
    (fragment : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hTokenSafe : SurfaceText.AtomSafe token)
    (hElaborate : ∀ (fuel callPosition atomPosition : Nat), 0 < fuel →
      elaborateRawFuel context resolveHexKey fuel
        (.call callPosition name [.atom atomPosition token]) = .ok fragment) :
    CanonicalExprCorrect context
      (.call name [.atom token]) fragment := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp only [List.mem_singleton] at hMem
    subst argument
    unfold SurfaceText.Expr.AtomsSafe
    exact hTokenSafe
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨raw, rfl, hRaw⟩ :=
      rawExprMap_eq_singleton rawArguments (.atom token) hMap
    cases raw with
    | atom atomPosition rawToken =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel callPosition atomPosition (by omega)
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call => simp [RawSurfaceExpr.toExpr] at hRaw

private theorem canonicalExprCorrect_keyCall
    (context : ScriptContext) (name : String) (key : PubKey)
    (fragment : SurfaceFragment)
    (hValid : validResolvedPubKey context key)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hElaborate : ∀ (fuel callPosition atomPosition : Nat), 0 < fuel →
      elaborateRawFuel context resolveHexKey fuel
        (.call callPosition name [.atom atomPosition (prettyPubKey key)]) =
          .ok fragment) :
    CanonicalExprCorrect context
      (.call name [.atom (prettyPubKey key)]) fragment := by
  apply canonicalExprCorrect_unaryAtomCall
  · exact hNameSafe
  · apply atomSafe_byteArrayHex
    unfold validResolvedPubKey at hValid
    unfold PubKey.size at hValid
    cases context <;> omega
  · exact hElaborate

private theorem canonicalExprCorrect_pk
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk" [.atom (prettyPubKey key)]) (.pk key) := by
  apply canonicalExprCorrect_keyCall context "pk" key (.pk key) hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

private theorem canonicalExprCorrect_pkh
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pkh" [.atom (prettyPubKey key)]) (.pkh key) := by
  apply canonicalExprCorrect_keyCall context "pkh" key (.pkh key) hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

private theorem canonicalExprCorrect_pk_k
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk_k" [.atom (prettyPubKey key)]) (.core (.pk_k key)) := by
  apply canonicalExprCorrect_keyCall context "pk_k" key (.core (.pk_k key))
    hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

private theorem canonicalExprCorrect_pk_h
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk_h" [.atom (prettyPubKey key)]) (.core (.pk_h key)) := by
  apply canonicalExprCorrect_keyCall context "pk_h" key (.core (.pk_h key))
    hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

private theorem canonicalExprCorrect_older
    (context : ScriptContext) (value : Nat) :
    CanonicalExprCorrect context
      (.call "older" [.atom (toString value)]) (.core (.older value)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · exact atomSafe_toString value
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel]
        simp only [unaryArgument]
        simp
        change (fun result => SurfaceFragment.core (.older result)) <$>
          parseNatRaw "a relative timelock"
            (.atom atomPosition (toString value)) = .ok (.core (.older value))
        rw [parseNatRaw_toString "a relative timelock" atomPosition value]
        rfl

private theorem canonicalExprCorrect_after
    (context : ScriptContext) (value : Nat) :
    CanonicalExprCorrect context
      (.call "after" [.atom (toString value)]) (.core (.after value)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · exact atomSafe_toString value
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel]
        simp only [unaryArgument]
        simp
        change (fun result => SurfaceFragment.core (.after result)) <$>
          parseNatRaw "an absolute timelock"
            (.atom atomPosition (toString value)) = .ok (.core (.after value))
        rw [parseNatRaw_toString "an absolute timelock" atomPosition value]
        rfl

private theorem canonicalExprCorrect_sha256
    (context : ScriptContext) (hash : Hash256)
    (hValid : validHash256 hash) :
    CanonicalExprCorrect context
      (.call "sha256" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.sha256 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash256 Hash256.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "sha256" 32 atomPosition hash.bytes
            (by simpa [validHash256, Hash256.size] using hValid)]
        rfl

private theorem canonicalExprCorrect_hash256
    (context : ScriptContext) (hash : Hash256)
    (hValid : validHash256 hash) :
    CanonicalExprCorrect context
      (.call "hash256" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.hash256 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash256 Hash256.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "hash256" 32 atomPosition hash.bytes
            (by simpa [validHash256, Hash256.size] using hValid)]
        rfl

private theorem canonicalExprCorrect_ripemd160
    (context : ScriptContext) (hash : Hash160)
    (hValid : validHash160 hash) :
    CanonicalExprCorrect context
      (.call "ripemd160"
        [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.ripemd160 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash160 Hash160.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "ripemd160" 20 atomPosition hash.bytes
            (by simpa [validHash160, Hash160.size] using hValid)]
        rfl

private theorem canonicalExprCorrect_hash160
    (context : ScriptContext) (hash : Hash160)
    (hValid : validHash160 hash) :
    CanonicalExprCorrect context
      (.call "hash160" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.hash160 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash160 Hash160.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "hash160" 20 atomPosition hash.bytes
            (by simpa [validHash160, Hash160.size] using hValid)]
        rfl

private theorem canonicalExprCorrect_binaryCall
    (context : ScriptContext) (name : String)
    (firstExpr secondExpr : SurfaceText.Expr)
    (firstFragment secondFragment result : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hFirst : CanonicalExprCorrect context firstExpr firstFragment)
    (hSecond : CanonicalExprCorrect context secondExpr secondFragment)
    (hElaborate : ∀ (fuel callPosition : Nat)
      (firstRaw secondRaw : RawSurfaceExpr),
      elaborateRawFuel context resolveHexKey fuel firstRaw = .ok firstFragment →
      elaborateRawFuel context resolveHexKey fuel secondRaw = .ok secondFragment →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name [firstRaw, secondRaw]) = .ok result) :
    CanonicalExprCorrect context
      (.call name [firstExpr, secondExpr]) result := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp at hMem
    rcases hMem with rfl | rfl
    · exact hFirst.1
    · exact hSecond.1
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨firstRaw, secondRaw, rfl, hFirstRaw, hSecondRaw⟩ :=
      rawExprMap_eq_pair rawArguments firstExpr secondExpr hMap
    cases fuel with
    | zero => simp at hFuel
    | succ fuel =>
        have hFirstFuel : firstExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hSecondFuel : secondExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        exact hElaborate fuel callPosition firstRaw secondRaw
          (hFirst.2 fuel firstRaw hFirstRaw hFirstFuel)
          (hSecond.2 fuel secondRaw hSecondRaw hSecondFuel)

private theorem canonicalExprCorrect_ternaryCall
    (context : ScriptContext) (name : String)
    (firstExpr secondExpr thirdExpr : SurfaceText.Expr)
    (firstFragment secondFragment thirdFragment result : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hFirst : CanonicalExprCorrect context firstExpr firstFragment)
    (hSecond : CanonicalExprCorrect context secondExpr secondFragment)
    (hThird : CanonicalExprCorrect context thirdExpr thirdFragment)
    (hElaborate : ∀ (fuel callPosition : Nat)
      (firstRaw secondRaw thirdRaw : RawSurfaceExpr),
      elaborateRawFuel context resolveHexKey fuel firstRaw = .ok firstFragment →
      elaborateRawFuel context resolveHexKey fuel secondRaw = .ok secondFragment →
      elaborateRawFuel context resolveHexKey fuel thirdRaw = .ok thirdFragment →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name [firstRaw, secondRaw, thirdRaw]) = .ok result) :
    CanonicalExprCorrect context
      (.call name [firstExpr, secondExpr, thirdExpr]) result := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hFirst.1
    · exact hSecond.1
    · exact hThird.1
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨firstRaw, secondRaw, thirdRaw, rfl, hFirstRaw, hSecondRaw,
      hThirdRaw⟩ :=
      rawExprMap_eq_triple rawArguments firstExpr secondExpr thirdExpr hMap
    cases fuel with
    | zero => simp at hFuel
    | succ fuel =>
        have hFirstFuel : firstExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hSecondFuel : secondExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hThirdFuel : thirdExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        exact hElaborate fuel callPosition firstRaw secondRaw thirdRaw
          (hFirst.2 fuel firstRaw hFirstRaw hFirstFuel)
          (hSecond.2 fuel secondRaw hSecondRaw hSecondFuel)
          (hThird.2 fuel thirdRaw hThirdRaw hThirdFuel)

private def CanonicalExprListCorrect (context : ScriptContext)
    (exprs : List SurfaceText.Expr) (fragments : List SurfaceFragment) : Prop :=
  (∀ expr ∈ exprs, expr.AtomsSafe) ∧
    ∀ (fuel : Nat) (raws : List RawSurfaceExpr),
      raws.map RawSurfaceExpr.toExpr = exprs →
      (∀ expr ∈ exprs, expr.lexemes.length < fuel) →
        raws.mapM (elaborateRawFuel context resolveHexKey fuel) = .ok fragments

private theorem lexemes_length_le_argumentLexemes_of_mem
    (expr : SurfaceText.Expr) (arguments : List SurfaceText.Expr)
    (hMem : expr ∈ arguments) :
    expr.lexemes.length ≤ (SurfaceText.argumentLexemes arguments).length := by
  induction arguments with
  | nil => simp at hMem
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at hMem
          subst expr
          simp [SurfaceText.argumentLexemes]
      | cons next rest =>
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · simp [SurfaceText.argumentLexemes]
          · have hMemTail : expr ∈ next :: rest := by simpa using hMem
            have hTail := ih hMemTail
            simp [SurfaceText.argumentLexemes] at hTail ⊢
            omega

private theorem lexemes_length_lt_call_of_mem
    (name : String) (arguments : List SurfaceText.Expr)
    (expr : SurfaceText.Expr) (hMem : expr ∈ arguments) :
    expr.lexemes.length <
      (SurfaceText.Expr.call name arguments).lexemes.length := by
  have hLe := lexemes_length_le_argumentLexemes_of_mem expr arguments hMem
  simp [SurfaceText.Expr.lexemes]
  omega

private theorem canonicalKeyListCorrect
    (context : ScriptContext) (keys : List PubKey)
    (hValid : CoreFragment.allKeysValid context keys) :
    (∀ expr ∈ keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)),
      expr.AtomsSafe) ∧
    ∀ raws : List RawSurfaceExpr,
      raws.map RawSurfaceExpr.toExpr =
        keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) →
      raws.mapM (resolveKeyRaw context resolveHexKey) = .ok keys := by
  induction keys with
  | nil =>
      constructor
      · simp
      · intro raws hMap
        have : raws = [] := rawExprMap_eq_nil raws (by simpa using hMap)
        subst raws
        rfl
  | cons key keys ih =>
      simp only [CoreFragment.allKeysValid] at hValid
      have hKeyPositive : 0 < key.bytes.size := by
        unfold validResolvedPubKey PubKey.size at hValid
        cases context <;> omega
      have hTail := ih hValid.2
      constructor
      · intro expr hMem
        simp only [List.map_cons, List.mem_cons] at hMem
        rcases hMem with rfl | hMem
        · unfold SurfaceText.Expr.AtomsSafe
          exact atomSafe_byteArrayHex key.bytes hKeyPositive
        · exact hTail.1 expr hMem
      · intro raws hMap
        obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
          rawExprMap_eq_cons raws (.atom (prettyPubKey key))
            (keys.map (fun tailKey => .atom (prettyPubKey tailKey))) hMap
        cases raw with
        | atom position token =>
            simp only [RawSurfaceExpr.toExpr] at hRaw
            cases hRaw
            simp only [List.mapM_cons]
            rw [resolveKeyRaw_prettyPubKey context position key hValid.1]
            rw [hTail.2 rest hRest]
            rfl
        | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
        | call => simp [RawSurfaceExpr.toExpr] at hRaw

mutual
  private theorem coreExprCanonicalCorrect
      (context : ScriptContext) (wrappers : String)
      (fragment : CoreFragment)
      (hWrappers : CanonicalWrappers wrappers)
      (hWellFormed : fragment.WellFormed context) :
      CanonicalExprCorrect context
        (SurfaceText.coreExprWithWrappers prettyPubKey wrappers fragment)
        (wrapSurfaceChain wrappers (normalizeCoreAsSurface fragment)) := by
    cases fragment with
    | zero =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers (.atom "0")
            (.core .zero) hWrappers (canonicalExprCorrect_zero context)
    | one =>
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers (.atom "1")
            (.core .one) hWrappers (canonicalExprCorrect_one context)
    | pk_k key =>
        have hBody := canonicalExprCorrect_pk_k context key hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | pk_h key =>
        have hBody := canonicalExprCorrect_pk_h context key hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | older value =>
        have hBody := canonicalExprCorrect_older context value
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | after value =>
        have hBody := canonicalExprCorrect_after context value
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | sha256 hash =>
        have hBody := canonicalExprCorrect_sha256 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | hash256 hash =>
        have hBody := canonicalExprCorrect_hash256 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | ripemd160 hash =>
        have hBody := canonicalExprCorrect_ripemd160 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | hash160 hash =>
        have hBody := canonicalExprCorrect_hash160 context hash hWellFormed
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | and_b first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hBody : CanonicalExprCorrect context
            (.call "and_b"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.and_b first second)) := by
          apply canonicalExprCorrect_binaryCall context "and_b" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.and_b (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_b first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_b"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_b first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_b" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_b (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_c first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_c"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_c first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_c" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_c (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | or_d first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_d"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_d first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_d" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_d (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
          canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | a inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "a") inner
          (canonicalWrappers_append_char wrappers 'a' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "a")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.a inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | s inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "s") inner
          (canonicalWrappers_append_char wrappers 's' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "s")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.s inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | d inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "d") inner
          (canonicalWrappers_append_char wrappers 'd' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "d")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.d inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | v inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "v") inner
          (canonicalWrappers_append_char wrappers 'v' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "v")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.v inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | j inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "j") inner
          (canonicalWrappers_append_char wrappers 'j' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "j")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.j inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | n inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "n") inner
          (canonicalWrappers_append_char wrappers 'n' hWrappers (by simp [CanonicalWrapper]))
          hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "n")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.n inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | and_v first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hBody : CanonicalExprCorrect context
            (.call "and_v"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.and_v first second)) := by
          apply canonicalExprCorrect_binaryCall context "and_v" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.and_v (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        cases second with
        | one =>
            have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "t") first
              (canonicalWrappers_append_char wrappers 't' hWrappers
                (by simp [CanonicalWrapper])) hWellFormed.1
            have hTarget : wrapSurfaceChain (wrappers ++ "t")
                (normalizeCoreAsSurface first) =
                wrapSurfaceChain wrappers (.t (normalizeCoreAsSurface first)) := by
              rw [wrapSurfaceChain_append]
              simp [wrapSurfaceChain, wrapSurface]
            rw [hTarget] at hRecursive
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | andor first second third =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2.1
        have hThird : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" third)
            (normalizeCoreAsSurface third) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" third
            canonicalWrappers_empty hWellFormed.2.2.1
        have hBody : CanonicalExprCorrect context
            (.call "andor"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second,
                SurfaceText.coreExprWithWrappers prettyPubKey "" third])
            (.core (.andor first second third)) := by
          apply canonicalExprCorrect_ternaryCall context "andor" _ _ _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · exact hThird
          · intro fuel position firstRaw secondRaw thirdRaw hFirstRaw hSecondRaw
              hThirdRaw
            simp [elaborateRawFuel, ternaryArguments]
            rw [hFirstRaw, hSecondRaw, hThirdRaw]
            change Except.ok (SurfaceFragment.core (.andor (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second))
              (desugar (normalizeCoreAsSurface third)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second,
              desugar_normalizeCoreAsSurface third]
        cases third with
        | zero =>
            have hSugar : CanonicalExprCorrect context
                (.call "and_n"
                  [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                    SurfaceText.coreExprWithWrappers prettyPubKey "" second])
                (.and_n (normalizeCoreAsSurface first)
                  (normalizeCoreAsSurface second)) := by
              apply canonicalExprCorrect_binaryCall context "and_n" _ _ _ _ _
              · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
                  SurfaceText.isPunctuation]
              · exact hFirst
              · exact hSecond
              · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
                simp [elaborateRawFuel, binaryArguments]
                rw [hFirstRaw, hSecondRaw]
                rfl
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers
                hSugar
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | c inner =>
        have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "c") inner
          (canonicalWrappers_append_char wrappers 'c' hWrappers
            (by simp [CanonicalWrapper])) hWellFormed
        have hTarget : wrapSurfaceChain (wrappers ++ "c")
            (normalizeCoreAsSurface inner) =
            wrapSurfaceChain wrappers (.core (.c inner)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface, desugar_normalizeCoreAsSurface]
        rw [hTarget] at hRecursive
        cases inner with
        | pk_k key =>
            have hBody := canonicalExprCorrect_pk context key hWellFormed
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
        | pk_h key =>
            have hBody := canonicalExprCorrect_pkh context key hWellFormed
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
              canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
        | _ =>
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
    | or_i first second =>
        have hFirst : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" first)
            (normalizeCoreAsSurface first) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" first
            canonicalWrappers_empty hWellFormed.1
        have hSecond : CanonicalExprCorrect context
            (SurfaceText.coreExprWithWrappers prettyPubKey "" second)
            (normalizeCoreAsSurface second) := by
          simpa [wrapSurfaceChain] using coreExprCanonicalCorrect context "" second
            canonicalWrappers_empty hWellFormed.2
        have hBody : CanonicalExprCorrect context
            (.call "or_i"
              [SurfaceText.coreExprWithWrappers prettyPubKey "" first,
                SurfaceText.coreExprWithWrappers prettyPubKey "" second])
            (.core (.or_i first second)) := by
          apply canonicalExprCorrect_binaryCall context "or_i" _ _ _ _ _
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · exact hFirst
          · exact hSecond
          · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
            simp [elaborateRawFuel, binaryArguments]
            rw [hFirstRaw, hSecondRaw]
            change Except.ok (SurfaceFragment.core (.or_i (desugar (normalizeCoreAsSurface first))
              (desugar (normalizeCoreAsSurface second)))) = _
            rw [desugar_normalizeCoreAsSurface first,
              desugar_normalizeCoreAsSurface second]
        have hRightRecursive := coreExprCanonicalCorrect context (wrappers ++ "u") first
          (canonicalWrappers_append_char wrappers 'u' hWrappers
            (by simp [CanonicalWrapper])) hWellFormed.1
        have hRightTarget : wrapSurfaceChain (wrappers ++ "u")
            (normalizeCoreAsSurface first) =
            wrapSurfaceChain wrappers (.u (normalizeCoreAsSurface first)) := by
          rw [wrapSurfaceChain_append]
          simp [wrapSurfaceChain, wrapSurface]
        rw [hRightTarget] at hRightRecursive
        cases first with
        | zero =>
            have hRecursive := coreExprCanonicalCorrect context (wrappers ++ "l") second
              (canonicalWrappers_append_char wrappers 'l' hWrappers
                (by simp [CanonicalWrapper])) hWellFormed.2
            have hTarget : wrapSurfaceChain (wrappers ++ "l")
                (normalizeCoreAsSurface second) =
                wrapSurfaceChain wrappers (.l (normalizeCoreAsSurface second)) := by
              rw [wrapSurfaceChain_append]
              simp [wrapSurfaceChain, wrapSurface]
            rw [hTarget] at hRecursive
            simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using hRecursive
        | _ =>
            cases second with
            | zero =>
                simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
                  hRightRecursive
            | _ =>
                simpa [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface] using
                  canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
    | thresh threshold fragments =>
        have hFragments := coreExprListCanonicalCorrect context fragments hWellFormed.2.1
        have hFragmentsNonempty : fragments ≠ [] := by
          intro hEmpty
          subst fragments
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedFragmentsNonempty :
            fragments.map
                (SurfaceText.coreExprWithWrappers prettyPubKey "") ≠ [] := by
          simpa using hFragmentsNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")) =
              .atom (toString threshold) ::
                fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "") :=
          SurfaceText.variadicArguments_of_ne_nil _ _
            hRenderedFragmentsNonempty
        have hBody : CanonicalExprCorrect context
            (.call "thresh"
              (.atom (toString threshold) ::
                fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")))
            (.core (.thresh threshold fragments)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hFragments.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (fragments.map
                  (SurfaceText.coreExprWithWrappers prettyPubKey "")) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hFragmentsNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
                    have hEach : ∀ expr ∈ fragments.map
                        (SurfaceText.coreExprWithWrappers prettyPubKey ""),
                        expr.lexemes.length < fuel := by
                      intro expr hMem
                      have hLess := lexemes_length_lt_call_of_mem "thresh"
                        (.atom (toString threshold) :: fragments.map
                          (SurfaceText.coreExprWithWrappers prettyPubKey ""))
                        expr (by simp [hMem])
                      omega
                    simp [elaborateRawFuel]
                    simp only [variadicArguments, hRestNonempty]
                    simp only [Bool.false_eq_true, if_false]
                    simp
                    rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
                    rw [hFragments.2 fuel rest hRest hEach]
                    have hDesugarMap :
                        (fragments.map normalizeCoreAsSurface).map desugar =
                          fragments := by
                      have hFunction :
                          (desugar ∘ normalizeCoreAsSurface) = id := by
                        funext fragment
                        exact desugar_normalizeCoreAsSurface fragment
                      rw [List.map_map, hFunction, List.map_id]
                    change Except.ok (SurfaceFragment.core (.thresh threshold
                      ((fragments.map normalizeCoreAsSurface).map desugar))) = _
                    rw [hDesugarMap]
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody
    | multi threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2.2
        have hKeysNonempty : keys ≠ [] := by
          intro hEmpty
          subst keys
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedKeysNonempty :
            keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) ≠ [] := by
          simpa using hKeysNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) =
              .atom (toString threshold) ::
                keys.map (fun key => .atom (prettyPubKey key)) :=
          SurfaceText.variadicArguments_of_ne_nil _ _ hRenderedKeysNonempty
        have hBody : CanonicalExprCorrect context
            (.call "multi" (.atom (toString threshold) ::
              keys.map (fun key => .atom (prettyPubKey key))))
            (.core (.multi threshold keys)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hKeys.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hKeysNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
                    cases context with
                    | tapscript =>
                        simp [CoreFragment.WellFormed,
                          ScriptContext.permitsLegacyMulti] at hWellFormed
                    | p2wsh =>
                        simp [elaborateRawFuel]
                        simp only [variadicArguments, hRestNonempty]
                        simp only [Bool.false_eq_true, if_false]
                        simp
                        rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
                        rw [hKeys.2 rest hRest]
                        rfl
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody
    | multi_a threshold keys =>
        have hKeys := canonicalKeyListCorrect context keys hWellFormed.2.2
        have hKeysNonempty : keys ≠ [] := by
          intro hEmpty
          subst keys
          simp [CoreFragment.WellFormed, validThreshold] at hWellFormed
          omega
        have hRenderedKeysNonempty :
            keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) ≠ [] := by
          simpa using hKeysNonempty
        have hVariadicArguments :
            SurfaceText.variadicArguments (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) =
              .atom (toString threshold) ::
                keys.map (fun key => .atom (prettyPubKey key)) :=
          SurfaceText.variadicArguments_of_ne_nil _ _ hRenderedKeysNonempty
        have hBody : CanonicalExprCorrect context
            (.call "multi_a" (.atom (toString threshold) ::
              keys.map (fun key => .atom (prettyPubKey key))))
            (.core (.multi_a threshold keys)) := by
          apply canonicalExprCorrect_call
          · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
              SurfaceText.isPunctuation]
          · intro argument hMem
            simp only [List.mem_cons] at hMem
            rcases hMem with rfl | hMem
            · unfold SurfaceText.Expr.AtomsSafe
              exact atomSafe_toString threshold
            · exact hKeys.1 argument hMem
          · intro fuel position raws hMap hFuel
            obtain ⟨thresholdRaw, rest, rfl, hThresholdRaw, hRest⟩ :=
              rawExprMap_eq_cons raws (.atom (toString threshold))
                (keys.map (fun key => .atom (prettyPubKey key))) hMap
            have hRestNonempty : rest.isEmpty = false := by
              cases rest with
              | nil =>
                  have := congrArg List.length hRest
                  simp at this
                  exact False.elim (hKeysNonempty
                    (List.length_eq_zero_iff.mp this.symm))
              | cons => rfl
            cases thresholdRaw with
            | atom thresholdPosition token =>
                simp only [RawSurfaceExpr.toExpr] at hThresholdRaw
                cases hThresholdRaw
                cases fuel with
                | zero => simp at hFuel
                | succ fuel =>
                    cases context with
                    | p2wsh =>
                        simp [CoreFragment.WellFormed,
                          ScriptContext.permitsCheckSigAddMulti] at hWellFormed
                    | tapscript =>
                        simp [elaborateRawFuel]
                        simp only [variadicArguments, hRestNonempty]
                        simp only [Bool.false_eq_true, if_false]
                        simp
                        rw [parseNatRaw_repr "a threshold" thresholdPosition threshold]
                        rw [hKeys.2 rest hRest]
                        rfl
            | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
            | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
        simp only [SurfaceText.coreExprWithWrappers, normalizeCoreAsSurface]
        rw [hVariadicArguments]
        exact canonicalExprCorrect_prependWrappers context wrappers _ _
          hWrappers hBody

  private theorem coreExprListCanonicalCorrect
      (context : ScriptContext) (fragments : List CoreFragment)
      (hWellFormed : CoreFragment.allWellFormed context fragments) :
      CanonicalExprListCorrect context
        (fragments.map (SurfaceText.coreExprWithWrappers prettyPubKey ""))
        (fragments.map normalizeCoreAsSurface) := by
    cases fragments with
    | nil =>
        constructor
        · simp
        · intro fuel raws hMap hFuel
          have : raws = [] := rawExprMap_eq_nil raws (by simpa using hMap)
          subst raws
          rfl
    | cons fragment fragments =>
        simp only [CoreFragment.allWellFormed] at hWellFormed
        have hHead := coreExprCanonicalCorrect context "" fragment
          canonicalWrappers_empty hWellFormed.1
        have hTail := coreExprListCanonicalCorrect context fragments hWellFormed.2
        constructor
        · intro expr hMem
          simp only [List.map_cons, List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · exact hHead.1
          · exact hTail.1 expr hMem
        · intro fuel raws hMap hFuel
          obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
            rawExprMap_eq_cons raws
              (SurfaceText.coreExprWithWrappers prettyPubKey "" fragment)
              (fragments.map
                (SurfaceText.coreExprWithWrappers prettyPubKey "")) hMap
          simp only [List.mapM_cons, List.map_cons]
          rw [hHead.2 fuel raw hRaw (hFuel _ (by simp))]
          rw [hTail.2 fuel rest hRest (by
            intro expr hMem
            exact hFuel expr (by simp [hMem]))]
          rfl
end

private theorem normalizedSurfaceExprCanonicalCorrect
    (context : ScriptContext) (wrappers : String)
    (fragment : SurfaceFragment)
    (hWrappers : CanonicalWrappers wrappers)
    (hWellFormed : fragment.WellFormed context) :
    CanonicalExprCorrect context
      (SurfaceText.normalizedExprWithWrappers prettyPubKey wrappers
        (normalizeSurface fragment))
      (wrapSurfaceChain wrappers (normalizeSurface fragment)) := by
  induction fragment generalizing wrappers with
  | core core =>
      simpa [normalizeSurface,
        SurfaceText.normalizedExpr_normalizeCoreAsSurface] using
        coreExprCanonicalCorrect context wrappers core hWrappers hWellFormed
  | pk key =>
      have hValid : validResolvedPubKey context key := by
        simpa [SurfaceFragment.WellFormed, desugar,
          SurfaceFragment.desugar, CoreFragment.WellFormed] using hWellFormed
      have hBody := canonicalExprCorrect_pk context key hValid
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | pkh key =>
      have hValid : validResolvedPubKey context key := by
        simpa [SurfaceFragment.WellFormed, desugar,
          SurfaceFragment.desugar, CoreFragment.WellFormed] using hWellFormed
      have hBody := canonicalExprCorrect_pkh context key hValid
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | and_n first second hFirst hSecond =>
      have hFirstWellFormed : first.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      have hSecondWellFormed : second.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.2.1
      have hFirstCorrect := hFirst "" canonicalWrappers_empty hFirstWellFormed
      have hSecondCorrect := hSecond "" canonicalWrappers_empty hSecondWellFormed
      have hBody : CanonicalExprCorrect context
          (.call "and_n"
            [SurfaceText.normalizedExprWithWrappers prettyPubKey ""
                (normalizeSurface first),
              SurfaceText.normalizedExprWithWrappers prettyPubKey ""
                (normalizeSurface second)])
          (.and_n (normalizeSurface first) (normalizeSurface second)) := by
        apply canonicalExprCorrect_binaryCall context "and_n" _ _ _ _ _
        · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
            SurfaceText.isPunctuation]
        · exact hFirstCorrect
        · exact hSecondCorrect
        · intro fuel position firstRaw secondRaw hFirstRaw hSecondRaw
          simp [elaborateRawFuel, binaryArguments]
          rw [hFirstRaw, hSecondRaw]
          rfl
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using
        canonicalExprCorrect_prependWrappers context wrappers _ _ hWrappers hBody
  | t inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      have hRecursive := ih (wrappers ++ "t")
        (canonicalWrappers_append_char wrappers 't' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "t")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.t (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive
  | l inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.2
      have hRecursive := ih (wrappers ++ "l")
        (canonicalWrappers_append_char wrappers 'l' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "l")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.l (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive
  | u inner ih =>
      have hInnerWellFormed : inner.WellFormed context := by
        simpa [SurfaceFragment.WellFormed] using hWellFormed.1
      have hRecursive := ih (wrappers ++ "u")
        (canonicalWrappers_append_char wrappers 'u' hWrappers
          (by simp [CanonicalWrapper])) hInnerWellFormed
      have hTarget : wrapSurfaceChain (wrappers ++ "u")
          (normalizeSurface inner) =
          wrapSurfaceChain wrappers (.u (normalizeSurface inner)) := by
        rw [wrapSurfaceChain_append]
        simp [wrapSurfaceChain, wrapSurface]
      rw [hTarget] at hRecursive
      simpa [normalizeSurface, SurfaceText.normalizedExprWithWrappers] using hRecursive

private def parseSurfaceUnchecked (context : ScriptContext)
    (resolver : KeyResolver) (input : String) :
    Except SurfaceParseError SurfaceFragment := do
  let tokens := tokenizeSurface input
  if tokens.isEmpty then
    .error .emptyInput
  else
    let (raw, remaining) ← parseRaw tokens
    match remaining with
    | token :: _ =>
        .error (.trailingInput token.position (tokenText token))
    | [] =>
        elaborateRawFuel context resolver (tokens.length + 1) raw

/-- Parse one supported Miniscript expression, resolve its keys, normalize its
    surface spelling, and reject fragments invalid in the selected context. -/
def parseSurface (context : ScriptContext) (resolver : KeyResolver)
    (input : String) : Except SurfaceParseError SurfaceFragment := do
  let fragment ← parseSurfaceUnchecked context resolver input
  validateSurface context (normalizeSurface fragment)

/-- Every successfully parsed surface fragment is already in canonical form. -/
theorem normalizeSurface_of_parseSurface_eq_ok
    (context : ScriptContext) (resolver : KeyResolver) (input : String)
    (fragment : SurfaceFragment)
    (h : parseSurface context resolver input = .ok fragment) :
    normalizeSurface fragment = fragment := by
  unfold parseSurface at h
  cases hUnchecked : parseSurfaceUnchecked context resolver input with
  | error error =>
      rw [hUnchecked] at h
      contradiction
  | ok unchecked =>
      rw [hUnchecked] at h
      change validateSurface context (normalizeSurface unchecked) = .ok fragment at h
      by_cases hValid : (normalizeSurface unchecked).WellFormed context
      · simp [validateSurface, hValid] at h
        change Except.ok (normalizeSurface unchecked) = Except.ok fragment at h
        injection h with hFragment
        rw [← hFragment]
        exact normalizeSurface_idempotent unchecked
      · simp [validateSurface, hValid] at h

/-- Parse canonical surface text whose key tokens are raw hexadecimal public
    keys. -/
def parseSurfaceHex (context : ScriptContext) (input : String) :
    Except SurfaceParseError SurfaceFragment :=
  parseSurface context resolveHexKey input

private theorem parseSurfaceUnchecked_prettySurface
    (context : ScriptContext) (fragment : SurfaceFragment)
    (hWellFormed : fragment.WellFormed context) :
    parseSurfaceUnchecked context resolveHexKey (prettySurface fragment) =
      .ok (normalizeSurface fragment) := by
  let expr := SurfaceText.normalizedExprWithWrappers prettyPubKey ""
    (normalizeSurface fragment)
  have hCorrect : CanonicalExprCorrect context expr
      (normalizeSurface fragment) := by
    simpa [expr, wrapSurfaceChain] using
      normalizedSurfaceExprCanonicalCorrect context "" fragment
        canonicalWrappers_empty hWellFormed
  let tokens := tokenizeSurface expr.render
  have hTokens : tokens.map SurfaceToken.toLexeme = expr.lexemes := by
    exact tokenizeSurface_renderExpr expr hCorrect.1
  have hTokensNonempty : tokens ≠ [] := by
    intro hEmpty
    have hExprEmpty : expr.lexemes = [] := by
      rw [← hTokens]
      simp [hEmpty]
    exact SurfaceText.Expr.lexemes_ne_nil expr hExprEmpty
  obtain ⟨raw, hParse, hRaw⟩ :=
    parseRaw_tokenizeSurface_renderExpr expr hCorrect.1
  have hLengths : tokens.length = expr.lexemes.length := by
    have := congrArg List.length hTokens
    simpa using this
  have hElaborate :
      elaborateRawFuel context resolveHexKey (tokens.length + 1) raw =
        .ok (normalizeSurface fragment) := by
    apply hCorrect.2
    · exact hRaw
    · omega
  unfold parseSurfaceUnchecked
  change (do
    if tokens.isEmpty then
      Except.error SurfaceParseError.emptyInput
    else
      let (raw, remaining) ← parseRaw tokens
      match remaining with
      | token :: _ =>
          Except.error (.trailingInput token.position (tokenText token))
      | [] => elaborateRawFuel context resolveHexKey (tokens.length + 1) raw) = _
  have hTokensIsEmpty : tokens.isEmpty = false := by
    cases hTokensValue : tokens with
    | nil => exact False.elim (hTokensNonempty hTokensValue)
    | cons => rfl
  rw [if_neg (by simpa using hTokensIsEmpty)]
  rw [hParse]
  exact hElaborate

/-- `parseSurfaceHex` is a left inverse of `prettySurface` for every
    context-valid surface fragment, modulo the documented surface
    normalization. -/
theorem parseSurfaceHex_prettySurface
    (context : ScriptContext) (fragment : SurfaceFragment)
    (hWellFormed : fragment.WellFormed context) :
    parseSurfaceHex context (prettySurface fragment) =
      .ok (normalizeSurface fragment) := by
  have hNormalizedWellFormed :
      (normalizeSurface fragment).WellFormed context := by
    unfold SurfaceFragment.WellFormed
    change (desugar (normalizeSurface fragment)).WellFormed context
    rw [desugar_normalizeSurface]
    exact hWellFormed
  unfold parseSurfaceHex parseSurface
  rw [parseSurfaceUnchecked_prettySurface context fragment hWellFormed]
  change validateSurface context (normalizeSurface (normalizeSurface fragment)) =
    .ok (normalizeSurface fragment)
  rw [normalizeSurface_idempotent]
  simp [validateSurface, hNormalizedWellFormed]
  rfl

end LeanMiniscript.Miniscript
