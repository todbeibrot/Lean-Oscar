import Mathlib
import Mrdi.Basic
import Mrdi.Stream
import Std

namespace Mrdi.Server

open Lean Meta Mrdi Json IO Process System Qq MrdiFile

initialize serverPath : FilePath ← do
  if System.Platform.isWindows then
    return ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"windows_test_server.jl"⟩
  return ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"server.jl"⟩

initialize juliaPath : FilePath ← do
  return ((← currentDir).join ⟨"Mrdi"⟩).join ⟨"julia.sh"⟩

private def childSpawnArgs : SpawnArgs :=
  { cmd := juliaPath.toString, args := #[serverPath.toString], stdin := .piped, stdout := .piped, stderr := .piped }

initialize juliaAccess : Std.Tactic.Cache (Child childSpawnArgs.toStdioConfig) ← Std.Tactic.Cache.mk (spawn childSpawnArgs)

/-- Is not necessary. The server will be started the first time we use `juliaAccess.get` -/
elab "#start_server" : command => do
  let child ← juliaAccess.get
  let (stdin, child) ← child.takeStdin
  (IO.FS.Stream.ofHandle stdin).putStrLn "start server"
  (IO.FS.Stream.ofHandle stdin).flush
  let stdout ← IO.asTask child.stdout.getLine
  let s ← IO.ofExcept stdout.get
  logInfo s
  return

elab "#endserver" : command => do
  let child ← juliaAccess.get
  let (stdin, child) ← child.takeStdin
  (IO.FS.Stream.ofHandle stdin).putStrLn "exit"
  (IO.FS.Stream.ofHandle stdin).flush
  let exitCode ← child.wait
  if exitCode != 0 then
    throwError "exit code not 0"
  return

/-- Sends the `command` and then the `mrdi` to the server and returns the returning Mrdi object -/
def julia (command : String) (mrdi : Mrdi) (trace : Bool := False) : MetaM Mrdi := do
  let child ← juliaAccess.get
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

/-- Sends the `command` and then the `val` to the server and returns the returns an `Expr` of type `α` object -/
def julia' (command : String) (val : Expr) {u} (α : Q(Type u)) (trace : Bool := False) : MetaM Expr := do
  let mrdi : Mrdi ← IO.MrdiFile.Mrdi? val
  let child ← juliaAccess.get
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
  evalMrdi α mrdi

/-- Sends the mrdi to julia and it should send it back -/
def echo (mrdi : Mrdi) : MetaM Mrdi := julia "echo" mrdi True

/-- Sends the mrdi to julia and it should send it back -/
elab "#echo " val:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM do
    let valE ← Lean.Elab.Term.elabTerm val none
    let α : Q(Type) ← inferType valE
    let mrdi ← IO.MrdiFile.Mrdi? valE
    let new_mrdi ← echo mrdi
    let new_val ← evalMrdi α new_mrdi
    let message ← PrettyPrinter.ppExpr new_val
    logInfo message

end Mrdi.Server
