import Mathlib

-- TODO Documentation
-- TODO UUIDs aren't just random numbers. They encode version and stuff like that. Does it matter?

def String.insertNth (s : String) (c : Char) (n : Nat) : String :=
  ⟨List.insertNth n c (s.toList)⟩

-- 2^128
def UUID.size := 340282366920938463463374607431768211456

def UUID := Fin 340282366920938463463374607431768211456
deriving Inhabited, DecidableEq, Lean.ToExpr, Fintype, BEq, LT, Ord

namespace UUID

instance (n : Nat) : OfNat UUID n := ⟨Fin.ofNat n⟩

section Repr

-- TODO show termination
private partial def fill_with_zeros (s : String) : String :=
  if s.length < 32 then fill_with_zeros (s.push '0') else s

private def add_minus (s : String) : String :=
  (((s.insertNth '-' 8).insertNth '-' 13).insertNth '-' 18).insertNth '-' 23

def hex_repr (n : Nat) : String :=
  (Nat.toDigits 16 n).asString

protected def repr (uuid : UUID) : String := add_minus $ fill_with_zeros $ hex_repr uuid.val

-- Do we need the Repr and ToString instances?
instance : Repr UUID := ⟨fun n _ => UUID.repr n⟩

instance : ToString UUID := ⟨fun uuid => UUID.repr uuid⟩

instance : Std.ToFormat UUID := ⟨fun uuid => UUID.repr uuid⟩

end Repr

section Parse

open Lean.Parsec Lean

partial def UUIDCore (acc digits : Nat) : Parsec (Nat × Nat) := do
  let some c ← peek? | return (acc, digits)
  if c == '-' then skip
  let n ← Json.Parser.hexChar
  let acc' := 16 * acc + n
  UUIDCore acc' (digits + 1)

def getUUID : Parsec Nat := do
  let (n, _) ← UUIDCore 0 0
  return n

def parse (s : String) : Except String UUID :=
  match getUUID s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok (OfNat.ofNat res)
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

end Parse

section Random

-- returns a random UUID
def IO.randUUID : IO UUID := do
  let n ← IO.rand 0 UUID.size
  return OfNat.ofNat n

-- returns a list with n random UUIDs
def IO.randUUIDs (n : ℕ) : IO (List UUID) :=
  (List.range n).mapM (fun _ => IO.randUUID)

end Random

end UUID
