import Mathlib
import Mrdi.mrdi
import Mrdi.randomstuff
import Mrdi.fromMrdi
import Mrdi.toMrdi
import Mrdi.stream
import Std
import Mrdi.oscar

open Lean Meta Mrdi Json IO IO.Process System Qq

initialize server_path : FilePath ← do
  return ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"server.jl"⟩

def child_spawn_args : SpawnArgs :=
  { cmd := "julia", args := #[server_path.toString], stdin := .piped, stdout := .piped, stderr := .piped }

initialize julia_access : Std.Tactic.Cache (Child child_spawn_args.toStdioConfig) ← Std.Tactic.Cache.mk (spawn child_spawn_args)

-- is not necessary. the server will be started the first time we use `julia_access.get`
elab "#start_server" : command => do
  let child ← julia_access.get
  let (stdin, child) ← child.takeStdin
  (IO.FS.Stream.ofHandle stdin).putStrLn "start server"
  (IO.FS.Stream.ofHandle stdin).flush
  let stdout ← IO.asTask child.stdout.getLine
  let s ← IO.ofExcept stdout.get
  logInfo s
  return

elab "#endserver" : command => do
  let child ← julia_access.get
  let (stdin, child) ← child.takeStdin
  (IO.FS.Stream.ofHandle stdin).putStrLn "exit"
  (IO.FS.Stream.ofHandle stdin).flush
  -- let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  -- let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then
    throwError "exit code not 0"
  return

def julia (command : String) (mrdi : Mrdi) (trace : Bool := False) : MetaM Mrdi := do
  let child ← julia_access.get
  let (stdin, child) ← child.takeStdin
  let stdin_stream := IO.FS.Stream.ofHandle stdin
  stdin_stream.putStrLn command
  stdin_stream.flush
  IO.FS.Stream.writeMrdi stdin_stream mrdi
  let stdout ← IO.asTask child.stdout.getLine
  let s ← IO.ofExcept stdout.get
  if s.startsWith "Error:" then
    throwError ("Error in julia: " ++ s)
  if trace then logInfo s
  let mrdi ← IO.ofExcept (Mrdi.parse s)
  return mrdi

def julia' (command : String) (val : Expr) {u} (α : Q(Type u)) (trace : Bool := False) : MetaM Expr := do
  let mrdi : Mrdi ← IO.MrdiFile.Mrdi? val
  let child ← julia_access.get
  let (stdin, child) ← child.takeStdin
  let stdin_stream := IO.FS.Stream.ofHandle stdin
  stdin_stream.putStrLn command
  stdin_stream.flush
  IO.FS.Stream.writeMrdi stdin_stream mrdi
  let stdout ← IO.asTask child.stdout.getLine
  let s ← IO.ofExcept stdout.get
  if s.startsWith "Error:" then
    throwError ("Error in julia: " ++ s)
  if trace then logInfo s
  let mrdi ← IO.ofExcept (Mrdi.parse s)
  let val : Q($α) ← IO.MrdiFile.eval_mrdi α mrdi
  let _ ← synthInstanceQ q(ToExpr $α)
  let e := q(toExpr $val)
  unsafe evalExpr Expr q(Expr) e

-- sends the mrdi to julia and it should send it back
def echo (mrdi : Mrdi) : MetaM Mrdi := do
  return ← julia "echo" mrdi True

elab "#echo " val:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM do
    let valE ← Lean.Elab.Term.elabTerm val none
    let α : Q(Type) ← inferType valE
    let mrdi ← IO.MrdiFile.Mrdi? valE
    let new_mrdi ← echo mrdi
    let new_val ← IO.MrdiFile.eval_mrdi α new_mrdi
    let message ← PrettyPrinter.ppExpr new_val
    logInfo message
    unless ← isDefEq valE new_val do
      throwError "The values are not definitionally equal"
    return

-- debugging stuff
elab "#test1" s:str : command => do
  let s2 : String := toString s
  let child ← julia_access.get
  let (stdin, child) ← child.takeStdin
  (IO.FS.Stream.ofHandle stdin).putStrLn s2
  (IO.FS.Stream.ofHandle stdin).flush
  let stdout ← IO.asTask child.stdout.getLine
  let s ← IO.ofExcept stdout.get
  logInfo s
  return
