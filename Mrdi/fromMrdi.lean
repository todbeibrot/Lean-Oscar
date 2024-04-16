import Mathlib
import Mrdi.Basic

namespace Mrdi

open Lean Json

-- TODO so far we use the data to get what we expect without caring if the ocject we get is of the expected type.
-- shouldnt change anything but we could give better error messages

-- In julia we start counting at 1 not 0. So some data has to be shifted
def MinusOneShift : Mrdi.Data → Mrdi.Data := Mrdi.Data.map
  fun s => match String.toNat? s with
    | some n => toString (n - 1)
    | none => s

class FromMrdiData (α : Type u) where
  fromMrdiData? : Mrdi.Data → Except String α

export FromMrdiData (fromMrdiData?)

instance : FromMrdiData ℕ where
  fromMrdiData? data := do
    let s ← Mrdi.Data.getStr? data
    let some n := String.toNat? s
      | throw s!"expected a string-encoded natural number, got '{s}'"
    return n

instance : FromMrdiData ℤ where
  fromMrdiData? data := do
    let s ← Mrdi.Data.getStr? data
    let some v := String.toInt? s
      | throw s!"expected a string-encoded integer, got '{s}'"
    return v

instance : FromMrdiData (Fin (n + 1)) where
  fromMrdiData? data := do
    let n : ℕ ← fromMrdiData? data
    return Fin.ofNat n

instance : FromMrdiData Bool where
  fromMrdiData? data := do
    let s ← Mrdi.Data.getStr? data
    match s with
      | "true" => return true
      | "false" => return false
      | _ => throw s!"expected a string-encoded boolean, got '{s}'"

instance : FromMrdiData String where
  fromMrdiData? data := Mrdi.Data.getStr? data

instance : FromMrdiData ℚ where
  fromMrdiData? data := do
    let s ← Mrdi.Data.getStr? data
    let l := s.splitOn "//"
    if l.length == 1 then do
      let some z := String.toInt? s
        | throw s!"expected a string-encoded integer, got '{s}'"
      return (z : ℚ)
    else if l.length == 2 then do
      let some z₀ := String.toInt? l[0]!
        | throw s!"expected a string-encoded integer, got '{l[0]!}'"
      let some z₁ := String.toInt? l[1]!
        | throw s!"expected a string-encoded integer, got '{l[1]!}'"
      return z₀ / z₁
    else
      throw s!"expected a string-encoded rational, got '{s}'"

instance [FromMrdiData α] : FromMrdiData (Array α) where
  fromMrdiData? data := do
    let a ← data.getArr?
    Array.mapM (fromMrdiData? (α := α)) a

instance [FromMrdiData α] : FromMrdiData (List α) where
  fromMrdiData? data := do
    let a : Array α ← fromMrdiData? data
    return a.toList

-- TODO better names for variables
noncomputable instance [Semiring R] [FromMrdiData R] : FromMrdiData (Polynomial R) where
  fromMrdiData? data := do
    let mut p : List $ Polynomial R := []
    let monomials ← data.getArr?
    for mono in monomials do
      let a ← mono.getArr?
      let n : Nat ← fromMrdiData? a[0]!
      let c : R ← fromMrdiData? a[1]!
      p := Polynomial.monomial n c :: p
    return List.sum p

/- {
"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
"_type":"PermGroup",
"data":{"degree":"5","gens":[["2","3","4","5","1"],["2","1"]]},
"id":"8a381e0b-de9d-4461-9f0f-ab078a664955"
} -/

-- TODO clean up
-- TODO use FinEnum instead of Fin
-- TODO this instance is still untested
instance : FromMrdiData (Subgroup (Equiv.Perm (Fin (n + 1)))) where
  fromMrdiData? data := do
    -- TODO check n == degree
    let mut gs : List $ Cycle (Fin (n + 1)) := []
    let gens ← data.getObjVal? "gens"
    let gens := MinusOneShift gens
    let a_gens ← gens.getArr?
    for gen in a_gens do
      let mut g : List (Fin (n + 1)) := []
      let a_gen ← gen.getArr?
      for x in a_gen do
        let s : String ← x.getStr?
        let n' : Fin (n + 1) := Fin.ofNat $ s.toNat!
        g := n' :: g
      gs := g.reverse :: gs
    gs := gs.reverse
    -- TODO that is not a cycle! we have to define π : Fin n+1 → Fin n+1 by sending i to the i-th value in ?g
    -- the vector might be shorter then degree. the rest should be id
    let gs' : Set $ Cycle (Fin (n + 1)) := gs.toFinset
    -- TODO how to automatically generate a proof for nodup x?
    let gs''' := List.map (fun x => Cycle.formPerm x sorry) gs
    let gs'' : Set (Equiv.Perm (Fin (n + 1))) := gs'''.toFinset
    return Subgroup.closure gs''

/-
{
    "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
    "_type":{"name":"PermGroupElem","params":"fafce409-efd1-4d55-ac8b-2f0bce9c6919"},
    "data":["2","3","1"],
    "_refs":{"fafce409-efd1-4d55-ac8b-2f0bce9c6919":{
        "_type":"PermGroup",
        "data":{"degree":"5","gens":[["2","3","4","5","1"],["2","1"]]}
        }
    }
} -/

-- def PermOfVector  (v : Vector (Fin (n + 1)) (n + 1)) : Equiv.Perm (Fin (n + 1)) where
--   toFun a := v.get a
--   invFun a := Fin.ofNat (List.indexOf a v.toList)
--   left_inv := sorry
--   right_inv := sorry

def PermOfList  (l : List (Fin (n + 1))) : Equiv.Perm (Fin (n + 1)) where
  toFun a := l[a]?.getD a
  invFun a := (List.indexOf? a l).getD a
  left_inv := sorry
  right_inv := sorry

instance : FromMrdiData (Equiv.Perm (Fin (n + 1))) where
  fromMrdiData? data := do
    let l : List (Fin (n + 1)) ← fromMrdiData? (MinusOneShift data)
    return PermOfList l


/- {
    "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
    "_type":{"name":"FPGroupElem","params":"21a98100-c09d-49ce-aa63-c7475094f2b9"},
    "data":["1","3","2","-1","1","-1","2","1","1","-1"],
    "_refs":{"21a98100-c09d-49ce-aa63-c7475094f2b9":
        {
            "_type":"FPGroup",
            "data":{"X":{"GapType":"IsFreeGroup","wfilt":"IsLetterWordsFamily","names":["x1","x2"]}}
        }
    }
}  -/

-- data is x1³ * x2⁻¹ * ...

-- The list `l` should contain pairs.
-- So for `n : ℕ` the element `l[2 * n]` should represent an elemtent of a free group and `l[2 * n + 1]` its exponent
private def pairs  : List ℤ → Except String (List (ℤ × ℤ))
  | [] => return []
  | a₁ :: a₂ :: as => return (a₁, a₂) :: (← pairs as)
  | _ => throw "List has odd number of elements"

private def constructWord [FinEnum α] : List (ℤ × ℤ) → FreeGroup α
  | [] => 1
  | (a, e) :: as => (FreeGroup.of $ FinEnum.equiv.invFun (Fin.ofNat' (Int.toNat (a - 1)) sorry)) ^ e * constructWord  as

-- TODO Nonempty α should be enough to fill the sorry
-- TODO the number i in the data stands for the i-th element of the free group.
-- But this doesnt has to be the i-th element of FinEnum.
-- So basically this doesn't work
-- we probably have to change fromMrdiData and give it more infos.
-- or does it even matter?
-- maybe every order is ok and what matters is the hom : FreeGroup α → whatever
instance [FinEnum α] [Nonempty α] : FromMrdiData $ FreeGroup α
  where fromMrdiData? data := do
    let l : List ℤ ← fromMrdiData? data
    return constructWord (← pairs l).reverse


section vector

/- {
    "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
    "_type":{"name":"Vector","params":"Base.Int"},
    "data":["1","2","3"]
} -/

instance [FromMrdiData α] : FromMrdiData $ Vector α n where
  fromMrdiData? data := do
    let l : List α ← fromMrdiData? data
    if h : l.length = n then
      return ⟨l, h⟩
    else throw s!"data list doesn't have length {n}"

end vector


section matrix

/- {
    "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
    "_type":{"name":"Matrix","params":"Base.Int"},
    "data":[["1","2"],["3","4"]]
} -/

instance [FromMrdiData α] : FromMrdiData $ Matrix (Fin m) (Fin n) α where
  fromMrdiData? data := do
    let v : Vector (Vector α n) m ← fromMrdiData? data
    return Matrix.of (fun x y => (v.get x).get y)

end matrix




class FromMrdi (α : Type u) where
  fromMrdi? : Mrdi → Except String α

export FromMrdi (fromMrdi?)

def fromMrdiD [FromMrdi α] [Inhabited α] (mrdi : Mrdi) : α :=
  match fromMrdi? mrdi with
    | .ok v => v
    | .error _ => default

-- is supposed to make it easier to define α if we havn't α but somethin of type α.
def fromMrdi?' [FromMrdi α] (mrdi : Mrdi) : α → Except String α :=
  fun _ => (fromMrdi? mrdi (α := α))

instance [FromMrdiData α] : FromMrdi α where
  fromMrdi? mrdi := do
    let data ← mrdi.data!
    fromMrdiData? data


end Mrdi
