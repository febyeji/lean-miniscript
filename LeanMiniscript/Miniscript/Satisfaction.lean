import LeanMiniscript.Miniscript.Syntax
import LeanMiniscript.Miniscript.Types
import LeanMiniscript.Miniscript.Witness

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- A typed hashlock target for preimage lookup. -/
inductive HashLock where
  | sha256 : Hash256 → HashLock
  | hash256 : Hash256 → HashLock
  | ripemd160 : Hash160 → HashLock
  | hash160 : Hash160 → HashLock

namespace HashLock

/-- The cryptographic relation required of a supplied preimage. Hash functions
    remain opaque at the formal boundary. -/
def Matches : HashLock → StackElement → Prop
  | .sha256 expected, preimage =>
      LeanMiniscript.Script.sha256 preimage = expected.bytes
  | .hash256 expected, preimage =>
      LeanMiniscript.Script.hash256 preimage = expected.bytes
  | .ripemd160 expected, preimage =>
      LeanMiniscript.Script.ripemd160 preimage = expected.bytes
  | .hash160 expected, preimage =>
      LeanMiniscript.Script.hash160 preimage = expected.bytes

end HashLock

/-- An environment provides the "real-world" data needed for satisfaction:
    concrete signatures, preimages, and the transaction context. -/
structure SatEnv where
  /-- Return the exact stack element to use as a signature, when available. -/
  signatureFor : PubKey → Option StackElement
  /-- Return the exact preimage stack element for a typed hashlock. -/
  preimageFor : HashLock → Option StackElement
  /-- Transaction data used by signature and timelock checks. -/
  txCtx : TxContext

namespace SatEnv

/-- Every piece of material returned by an environment satisfies the abstract
    cryptographic boundary used by `Eval`. -/
def Sound (env : SatEnv) : Prop :=
  (∀ key signature,
      env.signatureFor key = some signature →
      checkSig signature key.bytes env.txCtx.sigHash = true) ∧
  (∀ key : PubKey,
      checkSig falseElement key.bytes env.txCtx.sigHash = false) ∧
  (∀ lock preimage,
      env.preimageFor lock = some preimage →
      lock.Matches preimage)

end SatEnv

/-- Satisfaction result. -/
inductive SatResult where
  | sat : Witness → SatResult       -- Can satisfy with this witness
  | dissat : Witness → SatResult    -- Can dissatisfy with this witness
  | impossible : SatResult           -- Cannot satisfy or dissatisfy
  deriving Repr

/-- Compute a satisfaction witness for the currently supported basic B-type
    fragments. Timelocks consult the same transaction predicates as `Eval`, and
    signatures are returned in serialized witness order. Composite fragments
    and hashlocks remain unsupported until their candidate-selection rules are
    represented explicitly. -/
def satisfy : CoreFragment → SatEnv → Option Witness
  | .one, _ => some []
  | .c (.pk_k key), env => List.singleton <$> env.signatureFor key
  | .older n, env => if sequenceSatisfied n env.txCtx then some [] else none
  | .after n, env => if locktimeSatisfied n env.txCtx then some [] else none
  | _, _ => none

/-- Compute a clean dissatisfaction witness for the currently supported basic
    B-type fragments. `0` needs no witness; `c(pk_k)` uses the canonical empty
    signature whose failure is part of `SatEnv.Sound`. -/
def dissatisfy : CoreFragment → SatEnv → Option Witness
  | .zero, _ => some []
  | .c (.pk_k _), _ => some [falseElement]
  | _, _ => none

-- TODO(theorem): Extend satisfaction and dissatisfaction correctness through
-- hashlocks, wrappers, connectives, thresholds, `multi`, and `multi_a`.
-- TODO: Analyze non-malleable satisfaction (unique canonical witness)

end LeanMiniscript.Miniscript
