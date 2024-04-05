prelude
import Lean.Meta.Check
import Qq

/- @[extern "lean_eval_const"]
unsafe opaque evalConst (α) (env : @& Environment) (opts : @& Options) (constName : @& Name)
: Except String α
 -/

open Lean

unsafe def evalConst' (α) (env : Environment) (opts : Options) (αName constName : Name) : Except String α := do
  let x ← Lean.Environment.evalConst Type env opts αName

  let y ← Lean.Environment.evalConst α env opts constName
  let z ← Lean.Environment.evalConst α env opts constName
  return z


namespace Lean

unsafe def evalConst' [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (αName constName : Name) : m Unit := do
  let env ← getEnv
  let opts ← getOptions
  --let α : Type ← Lean.Environment.evalConst Type env opts αName
  --ofExcept <| (← getEnv).evalConst α (← getOptions) constName
  return

end Lean


namespace Lean.Meta

unsafe def evalExprCore'' (α) (value : Expr) (checkType : Expr → MetaM Unit) (safety := DefinitionSafety.safe) : MetaM α :=
  withoutModifyingEnv do
    let name ← mkFreshUserName `_tmp
    let value ← instantiateMVars value
    if value.hasMVar then
      throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
    let type ← inferType value
    checkType type
    let decl := Declaration.defnDecl {
       name, levelParams := [], type
       value, hints := ReducibilityHints.opaque,
       safety
    }
    addAndCompile decl
    evalConst α name

unsafe def evalExpr'' (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α :=
  evalExprCore (safety := safety) α value fun type => do
    unless ← isDefEq type expectedType do
      throwError "unexpected type at `evalExpr` {← mkHasTypeButIsExpectedMsg type expectedType}"

end Lean.Meta
