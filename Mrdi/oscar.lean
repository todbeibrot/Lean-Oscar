import Mathlib
import Mrdi.mrdi
import Mrdi.randomstuff
import Mrdi.fromMrdi
import Mrdi.toMrdi
import Mrdi.stream

namespace oscar

open Lean Meta Elab Tactic PrettyPrinter Parser Mrdi Json IO IO.Process System

initialize registerTraceClass `Meta.Tactic.oscar

def getMrdiFilePath (s : String) : IO FilePath := do
  let current_dir ← currentDir
  let mrdi_files_dir := current_dir.join ⟨"mrdi-files"⟩
  let file := mrdi_files_dir.join ⟨s ++ ".mrdi"⟩
  return file

def execute_julia (args : Array String) (mrdi : Mrdi) : IO Mrdi := do
  let path := ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"oscar.jl"⟩
  unless ← path.pathExists do
    throw <| IO.userError "could not find julia script Mrdi/oscar.jl"
  let child ← spawn
    { cmd := "julia", args := #[path.toString] ++ args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  IO.FS.Stream.writeMrdi (IO.FS.Stream.ofHandle stdin) mrdi
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then
    throw $ IO.userError stderr
  else
    let s ← IO.ofExcept stdout.get
    IO.ofExcept (Mrdi.parse s)

def load_mrdi_file (args : Array String) : IO Mrdi := do
  let path := ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"oscar.jl"⟩
  unless ← path.pathExists do
    throw <| IO.userError "could not find julia script Mrdi/oscar.jl"
  let out ← IO.Process.output { cmd := "julia", args := #[path.toString] ++ args }
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"Mrdi/oscar.jl exited with code {out.exitCode}:\n\n{out.stderr}"
  dbg_trace f!"out.stdout: {out.stdout}"
  match Json.parse out.stdout >>= dbg_trace f!"out.stdout: {out.stdout}"; fromJson? with
    | Except.ok v => dbg_trace f!"v: {v}"; return v
    | Except.error e => throw <| IO.Error.userError e

def send_args_and_print (args : Array String) : IO Unit := do
  let path := ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"oscar.jl"⟩
  unless ← path.pathExists do
    throw <| IO.userError "could not find julia script Mrdi/oscar.jl"
  let out ← IO.Process.output { cmd := "julia", args := #[path.toString] ++ args }
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"Mrdi/oscar.jl exited with code {out.exitCode}:\n\n{out.stderr}"
  dbg_trace f!"out.stdout: {out.stdout}"


def oscar : TacticM Unit := do
  --let mrdi ← load_mrdi_file
  --dbg_trace f!"value: {mrdi}"
  return

syntax "oscar" : tactic
elab_rules : tactic
  | `(tactic| oscar%$tk) => do
    let command ← `(tactic| oscar%$tk)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.oscar
    let _ ← oscar
    if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion command command --the second doesnt make sense




def eq_witness (g : MVarId) : TacticM ℤ :=
  g.withContext do
    -- let t ← g.getType
    -- -- can we make cleaner code by using Q() and q()?
    -- let some (_, fun_x_hx) := t.app2? ``Exists | throwError "not an existential statement"
    -- let some (_, hx) := fun_x_hx.lambda? | throwError "not a lambda"
    --let some (α, lhs, rhs) := hx.eq? | throwError "not an equality"
    return 5

-- TODO generalize giving a witness

/- is supposed to solve terms of type `∃x, a[x] = b[x]` -/
syntax "eq_witness" : tactic
elab_rules : tactic
  | `(tactic| eq_witness%$tk) => do
    let command ← `(tactic| eq_witness%$tk)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.oscar
    let goal ← getMainGoal
    let z ← eq_witness goal
    let witness ← `(term| $(Unhygienic.run `($(quote z))))
    let new_command ← `(tactic| use $witness:term)
    if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion command new_command
    -- else Elab.runTactic goal new_command
    -- the else case has to be in the tactic. not in elab_rules
    -- check what to move to the tactic




open Qq

/- this tactic is for debugging toMrdi and fromMrdi instances -/
def testint (val : TSyntax `term) : TacticM (TSyntax `term) := do
  let mrdi ← load_mrdi_file #["testint", ""]
  let int : Except String Int := FromMrdi.fromMrdi? mrdi --| throw "not an int"
  match int with
    | Except.ok v => do
        dbg_trace f!"v: {v}"
        -- TODO check how quote works
        let valE2_stx ← pure (quote v)
        return valE2_stx
    | Except.error e => dbg_trace f!"e: {e}"; return val

syntax "testint " term : tactic
elab_rules : tactic
  | `(tactic| testint%$tk $val) => do
    let command ← `(tactic| testint%$tk $val)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.oscar
    let v ← testint val
    let new_command ← `(tactic| use $v:term)
    if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion command new_command

-- TODO better name
def x {u} {α : Q(Type u)} (e : Q(Except String $α)) : MetaM Q($α) :=
  match e with
  | ~q(Except.ok $v) => return q($v)
  | ~q(Except.error $e) => throwError q($e)

/- this tactic is for debugging toMrdi and fromMrdi instances -/
def echo (val_stx: TSyntax `term) (valE : Expr) : MetaM (TSyntax `term) := do
  let α : Q(Type) ← inferType valE
  let eval_mrdi ← IO.MrdiFile.Mrdi? valE
  let new_mrdi ← execute_julia #["echo"] eval_mrdi
  let _ ← synthInstanceQ q(FromMrdi $α)
  let new_mrdiE : Q(Mrdi) := toExpr new_mrdi
  let new_valE : Q(Except String $α) := q(FromMrdi.fromMrdi? $new_mrdiE)
  let new_valE2 : Q(Except String $α) ← reduce new_valE
  let new_valE3 ← x new_valE2
  -- TODO use ppExpr instead of Quote
  -- TODO let user choose if he wants to replace by "try _" message
  let i1 ← synthInstanceQ q(Quote $α)
  let new_val_stxE := q(Quote.quote (self := $i1) $new_valE3)
  let new_val_stx ← unsafe evalExpr (TSyntax `term) q(TSyntax `term) new_val_stxE
  return new_val_stx

syntax "echo " term : tactic
elab_rules : tactic
  | `(tactic| echo%$tk $val) => do
    let command ← `(tactic| echo%$tk $val)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.oscar
    let valE ← elabTerm val none
    let v ← echo val valE
    let new_command ← `(tactic| use $v:term)
    if !traceMe then Lean.Meta.Tactic.TryThis.addSuggestion command new_command

example : ∃x, 5 + x = 10 := by
  --eq_witness
  --testint (10 : ℤ)
  --echo (0.2 : ℚ)
  use 5

end oscar
