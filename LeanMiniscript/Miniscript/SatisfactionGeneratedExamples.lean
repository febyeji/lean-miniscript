import LeanMiniscript.Miniscript.SatisfactionGeneratedProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Constants expose typed candidate-wide execution support even when one side
    of the pair is impossible. -/
example (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags) :
    (satisfactionCandidates .one env).SupportsGenerated scriptCtx .one
      ⟨.B, { z := true, u := true }⟩ flags env.txCtx :=
  generated_one scriptCtx env flags

/-- Candidate support projects directly through the public witness API. -/
example (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags)
    {witness : Witness} (selected : satisfy .one env = some witness) :
    GeneratedExecution .one witness true flags env.txCtx .B :=
  (generated_one scriptCtx env flags).satisfyExecution selected

/-- The K carrier records the pending signature, so wrapper `c` can consume it
    without changing the candidate pair. -/
example {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound)
    (encodings : env.EncodingSound flags)
    (emptyEncoding : checkSigEncodingFor flags env.txCtx.sigVersion
      falseElement key.bytes = .ok ()) :
    (satisfactionCandidates (.c (.pk_k key)) env).SupportsGenerated scriptCtx
      (.c (.pk_k key))
      ⟨.B, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx := by
  simpa using (generated_pk_k sound encodings emptyEncoding).c

/-- The shared hash theorem covers each concrete hash constructor while its
    DONTUSE dissatisfaction remains absent from the public projection. -/
example {scriptCtx : ScriptContext} {hash : Hash256} {env : SatEnv}
    {flags : ScriptFlags} (sound : env.Sound) :
    (satisfactionCandidates (.sha256 hash) env).SupportsGenerated scriptCtx
      (.sha256 hash) ⟨.B, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_hash (lock := .sha256 hash) sound

/-- Well-formed timelocks no longer need caller-supplied codec premises at the
    generated-candidate boundary. -/
example (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags) :
    (satisfactionCandidates (.older 10) env).SupportsGenerated scriptCtx
      (.older 10) ⟨.B, { z := true }⟩ flags env.txCtx :=
  generated_older ⟨by omega, by change 10 < 2147483648; omega⟩

example (scriptCtx : ScriptContext) (env : SatEnv) (flags : ScriptFlags) :
    (satisfactionCandidates (.after 500000000) env).SupportsGenerated scriptCtx
      (.after 500000000) ⟨.B, { z := true }⟩ flags env.txCtx :=
  generated_after ⟨by omega, by change 500000000 < 2147483648; omega⟩

/-- Context validity and modeled execution settings discharge the empty-signature
    encoding premise while retaining the original explicit theorem. -/
example {scriptCtx : ScriptContext} {key : PubKey} {env : SatEnv}
    {flags : ScriptFlags} (valid : validResolvedPubKey scriptCtx key)
    (version : ModeledContextVersion scriptCtx env.txCtx)
    (modeled : ModeledContextFlags scriptCtx flags)
    (sound : env.Sound) (encodings : env.EncodingSound flags) :
    (satisfactionCandidates (.pk_k key) env).SupportsGenerated scriptCtx
      (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩
      flags env.txCtx :=
  generated_pk_k_of_modeled valid version modeled sound encodings

end LeanMiniscript.Miniscript
