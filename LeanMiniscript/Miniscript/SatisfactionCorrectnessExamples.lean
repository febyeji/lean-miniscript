import LeanMiniscript.Miniscript.SatisfactionCorrectnessProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private abbrev guardedAndor : CoreFragment :=
  .andor (.d (.v .one)) .one .zero

/-- Surface `and_n` lowers to the guarded core `andor` fixture below. -/
private abbrev guardedAndN : SurfaceFragment :=
  .and_n (.core (.d (.v .one))) (.core .one)

private abbrev guardedAndorType : MiniType :=
  ⟨.B, { o := true, d := true, u := true }⟩

private theorem guardedAndorTyped :
    HasType .tapscript guardedAndor guardedAndorType := by
  exact .andor (.d_wrap (.v_wrap .one) rfl) rfl rfl .one .zero
    (by simp [branchBase]) rfl

private theorem guardedAndorWellFormed :
    CoreFragment.WellFormed .tapscript guardedAndor := by
  native_decide

private theorem guardedAndorValid :
    ValidMiniscript .tapscript guardedAndor :=
  ⟨guardedAndorType.mods,
    ⟨guardedAndorWellFormed, guardedAndorTyped⟩⟩

private theorem guardedAndorDissatisfiable :
    ValidDissatisfiableMiniscript .tapscript guardedAndor :=
  ⟨guardedAndorType.mods,
    ⟨guardedAndorWellFormed, guardedAndorTyped⟩, rfl⟩

private theorem guardedAndNDesugars : desugar guardedAndN = guardedAndor := by
  rfl

private theorem guardedAndNValid :
    ValidSurfaceMiniscript .tapscript guardedAndN := by
  simpa [ValidSurfaceMiniscript, guardedAndNDesugars] using guardedAndorValid

private theorem guardedAndNDissatisfiable :
    ValidDissatisfiableSurfaceMiniscript .tapscript guardedAndN := by
  simpa [ValidDissatisfiableSurfaceMiniscript, guardedAndNDesugars] using
    guardedAndorDissatisfiable

/-- The selected true guard executes the nested conditional to clean-stack
    acceptance. -/
example {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags) :
    Accepts .tapscript (compile guardedAndor) [trueElement]
      flags env.txCtx := by
  apply satisfactionCorrectnessCore guardedAndorValid sound encodings version
    modeled
  rfl

/-- The selected false guard skips the true branch and leaves a clean false
    result for the same nested core fragment. -/
example {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags) :
    Dissatisfies .tapscript (compile guardedAndor) [falseElement]
      flags env.txCtx := by
  apply dissatisfactionCorrectnessCore guardedAndorDissatisfiable sound
    encodings version modeled
  rfl

/-- Surface `and_n` satisfaction is transported through its `andor(_,_,0)`
    desugaring and leaves the selected true guard as the sole result. -/
example {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags) :
    Accepts .tapscript (compileSurface guardedAndN) [trueElement]
      flags env.txCtx := by
  apply satisfactionCorrectnessSurface guardedAndNValid sound encodings version
    modeled
  rfl

/-- The same surface sugar exposes its canonical false path through the core
    zero branch. -/
example {env : SatEnv} {flags : ScriptFlags}
    (sound : env.Sound) (encodings : env.EncodingSound flags)
    (version : ModeledContextVersion .tapscript env.txCtx)
    (modeled : ModeledContextFlags .tapscript flags) :
    Dissatisfies .tapscript (compileSurface guardedAndN) [falseElement]
      flags env.txCtx := by
  apply dissatisfactionCorrectnessSurface guardedAndNDissatisfiable sound
    encodings version modeled
  rfl

end LeanMiniscript.Miniscript
