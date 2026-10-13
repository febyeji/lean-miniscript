import LeanMiniscript.Miniscript.SurfaceParser

namespace LeanMiniscript.Miniscript

namespace SurfaceParser

/-!
# Surface parser proofs: tokenization and raw parsing

Rendering a surface expression and tokenizing the result recovers its lexemes,
and the raw parser reconstructs the expression from those tokens.

Some helpers here were `private` in the former single-file `SurfaceParserProofs`
module. They are visible only so that sibling submodules can use them; treat
them as internal proof helpers, not stable API.
-/

/-- Forget diagnostic positions after raw parsing. -/
def RawSurfaceExpr.toExpr : RawSurfaceExpr → SurfaceText.Expr
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


/-- Forget source positions after tokenization. This is the bridge from the
    diagnostic lexer to the position-free canonical grammar used by proofs. -/
def SurfaceToken.toLexeme (token : SurfaceToken) : SurfaceText.Lexeme :=
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

private theorem tokenizeCharsAcc_eq (position atomPosition : Nat)
    (reversedAtom : List Char) (reversedTokens : List SurfaceToken)
    (chars : List Char) :
    tokenizeCharsAcc position atomPosition reversedAtom reversedTokens chars =
      reversedTokens.reverse ++
        tokenizeChars position atomPosition reversedAtom chars := by
  induction chars generalizing position atomPosition reversedAtom reversedTokens with
  | nil =>
      cases reversedAtom <;>
        simp [tokenizeCharsAcc, pushTokenizedAtom, tokenizeChars,
          finishTokenizedAtom]
  | cons char rest ih =>
      simp only [tokenizeCharsAcc, tokenizeChars]
      split
      · cases reversedAtom <;>
          simp [pushTokenizedAtom, finishTokenizedAtom, ih,
            List.append_assoc]
      · split <;> cases reversedAtom <;>
          simp [pushTokenizedAtom, finishTokenizedAtom, ih,
            List.append_assoc]

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

private def lexemeIsPunctuation : SurfaceText.Lexeme → Prop
  | .atom _ => False
  | _ => True

private theorem tokenizeLexemeChars_afterAtom_punctuation
    (value : String) (punctuation : SurfaceText.Lexeme)
    (rest : List Char) (hNonempty : value.toList ≠ [])
    (hPunctuation : lexemeIsPunctuation punctuation) :
    tokenizeLexemeChars value.toList.reverse
        (punctuation.chars ++ rest) =
      .atom value :: tokenizeLexemeChars [] (punctuation.chars ++ rest) := by
  cases punctuation <;>
    simp_all [lexemeIsPunctuation, SurfaceText.Lexeme.chars,
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
              have hNext : lexemeIsPunctuation next := by
                cases next <;>
                  simp_all [LexemesTokenizable,
                    lexemeIsPunctuation]
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
    (hPunctuation : lexemeIsPunctuation punctuation)
    (hTail : LexemesTokenizable tail) :
    LexemesTokenizable (lexemes ++ punctuation :: tail) := by
  induction lexemes with
  | nil =>
      cases punctuation <;>
        simp_all [LexemesTokenizable, lexemeIsPunctuation]
  | cons lexeme lexemes ih =>
      cases lexeme <;> cases lexemes with
      | nil =>
          cases punctuation <;>
            simp_all [LexemesTokenizable, lexemeIsPunctuation]
      | cons next rest =>
          cases next <;> cases punctuation <;>
            simp_all [LexemesTokenizable, lexemeIsPunctuation]

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

theorem tokenizeSurface_renderExpr (expr : SurfaceText.Expr)
    (hSafe : expr.AtomsSafe) :
    (tokenizeSurface expr.render).map SurfaceToken.toLexeme = expr.lexemes := by
  rw [tokenizeSurface, SurfaceText.Expr.render, String.toList_ofList]
  rw [tokenizeCharsAcc_eq]
  simp only [List.reverse_nil, List.nil_append]
  rw [tokenizeChars_toLexemes]
  exact tokenizeLexemeChars_renderLexemes expr.lexemes
    (exprLexemesTokenizable expr hSafe)


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

theorem parseRaw_tokenizeSurface_renderExpr
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

end SurfaceParser

end LeanMiniscript.Miniscript
