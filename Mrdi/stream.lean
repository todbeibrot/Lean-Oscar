import Mrdi.mrdi
import Mrdi.toMrdi
import Mrdi.fromMrdi
import Init.System.IO

namespace IO.FS.Stream

open Lean
open IO

/-- Consumes `nBytes` bytes from the stream, interprets the bytes as a utf-8 string and the string as a valid Mrdi object. -/
def readMrdi (h : FS.Stream) (nBytes : Nat) : IO Mrdi := do
  let bytes ← h.read (USize.ofNat nBytes)
  let s := String.fromUTF8Unchecked bytes
  let json ← ofExcept (Json.parse s)
  let mrdi ← ofExcept (fromJson? json)
  return mrdi

def writeMrdi (h : FS.Stream) (mrdi : Mrdi) : IO Unit := do
  h.putStr (mrdi.compress ++ "\n")
  h.flush

end IO.FS.Stream

namespace IO.MrdiFile

open IO FS System Lean Lean.Elab Command Term Lean.Elab.Tactic
open Qq Tactic Meta Elab Parser PrettyPrinter Json Mrdi Command

def getMrdiFilePath (s : String) : IO FilePath := do
  let current_dir ← currentDir
  let mrdi_files_dir := current_dir.join ⟨"mrdi-files"⟩
  let file := mrdi_files_dir.join ⟨s ++ ".mrdi"⟩
  return file

def Mrdi? (val : Expr) : MetaM Mrdi := do
  let α : Q(Type) ← inferType val
  let val : Q($α) := val
  let _ ← synthInstanceQ q(ToMrdi $α)
  let uuids ← UUID.IO.randUUIDs 5   -- TODO how do we know how many uuids we actually need?
  let uuidsE : Q(List UUID) := toExpr uuids
  let mrdi := q(ToMrdi.toMrdi $uuidsE $val)
  unsafe evalExpr Mrdi q(Mrdi) mrdi

def eval_mrdi {u} (α : Q(Type u)) (mrdi : Mrdi) : MetaM Q($α) := do
  let mrdiE : Q(Mrdi) := toExpr mrdi
  let _ ← synthInstanceQ q(FromMrdi $α)
  let _ ← synthInstanceQ q(Inhabited $α)
  let val : Q($α) := q(fromMrdiD $mrdiE)
  instantiateMVars val

def eval_mrdi' (α) [FromMrdi α] (mrdi : Mrdi) : MetaM α := do
  return ← ofExcept (fromMrdi? mrdi)

def writeMrdi (fname : FilePath) (mrdi : Mrdi) : IO Unit :=
  writeFile fname (compress mrdi)

def readMrdi (fname : FilePath) : IO Mrdi :=
  readFile fname >>= (IO.ofExcept $ Mrdi.parse ·)

elab "#writeMrdi " val:term "to " file:term : command =>
  liftTermElabM do
    let valE : Expr ← elabTerm val none
    let mrdi : Mrdi ← Mrdi? valE
    let fileE : Q(String) ← elabTerm file q(String)
    let s ← unsafe evalExpr String q(String) fileE
    let path ← getMrdiFilePath s
    writeMrdi path mrdi

def load_mrdi_from_file (α : Q(Type)) (file : Q(String)) (trace : Bool := True) : MetaM Q($α) := do
  let s ← unsafe evalExpr String q(String) file
  let path ← getMrdiFilePath s
  let mrdi ← readMrdi path
  let valED ← eval_mrdi α mrdi
  if trace then
    logInfo (format mrdi)
    logInfo (format mrdi.data)
    let valE3 : Q($α) ← reduce valED
    try
      let _ ← synthInstanceQ q(Repr $α)
      let messageE : Q(Format) := q(repr $valE3)
      let message ← unsafe evalExpr Format q(Format) messageE
      logInfo message
    catch _ =>
      let message ← PrettyPrinter.ppExpr valE3
      logInfo "If you want a nice message, implement Repr"
      logInfo message
  return valED

elab "#readMrdi " type:term "from " file:term : command => do
  liftTermElabM do
    let α : Q(Type) ← elabTerm type q(Type)
    let fileE : Q(String) ← elabTerm file q(String)
    let _ ← load_mrdi_from_file α fileE
    return

end IO.MrdiFile
