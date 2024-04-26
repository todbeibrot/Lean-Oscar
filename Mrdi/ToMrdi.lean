import Mathlib
import Mrdi.Basic
import Mrdi.UUID
import Mrdi.ListToSet
import Qq

namespace Mrdi

open Lean Qq

variable (α : Type u)

section Basic

-- TODO
-- make a template wich can be used for copy and paste.
-- so I don't need to remember everything that has to be implemented

/-- In julia we start counting at 1 not 0. So some data has to be shifted -/
private def PlusOneShift : Mrdi.Data → Mrdi.Data := Mrdi.Data.map
  fun s => match String.toNat? s with
    | some n => toString (n + 1)
    | none => s


/-- `TypeWrapper` is wrapper for types to signal that we want the type `α` itself and not something of type `α` -/
-- TODO better names
inductive TypeWrapper
  | dummy
  | get_t (a : α)
  deriving Inhabited

-- TODO delete?
def Unwrap : TypeWrapper α → Type u := fun _ => α

/-- Encapsules data of type `α` -/
class ToData where
  toData : List UUID → α → MetaM Mrdi.Data

export ToData (toData)

-- TODO this instance is dangerous as it might construct wrong representations instead of raising an error.
-- should we keep it?
-- it works for String, Nat, Int, ...
instance [ToString α] : Mrdi.ToData α where
  toData _ a := return Data.str (toString a)

/-- Encapsules the type in Julia of elements of type `α` -/
class ToMrdiType where
  toMrdiType : List UUID → α → MetaM MrdiType

export ToMrdiType (toMrdiType)

class ToRef where
  toRef : List UUID → α → MetaM Mrdi

export ToRef (toRef)

class ToRefs where
  toRefs : List UUID → α → MetaM (Option (Lean.RBNode UUID fun _ => Mrdi)) := fun _ _ => return none

export ToRefs (toRefs)

-- If we don't specify an instance we assume that there are no references needed
instance : ToRefs α := ⟨fun _ _ => return none⟩

class ToMrdi where
  toMrdi : List UUID → α → MetaM Mrdi

export ToMrdi (toMrdi)

instance [Mrdi.ToData α] [ToMrdiType α] [ToRefs α] : ToMrdi α where
  toMrdi uuids a := return ⟨oscarNs, ← toMrdiType uuids a, ← toData uuids a, ← toRefs uuids a, none⟩

-- uuids[0] will be the id for this object
instance [ToRef α] [Inhabited α] : ToMrdi $ TypeWrapper α where
  toMrdi uuids _ := return (← toRef uuids (default : α)).setId uuids[0]!

instance [ToMrdi $ TypeWrapper α] : ToRef α where
  toRef uuids a := toMrdi uuids (TypeWrapper.get_t a)

end Basic

open TypeWrapper

section Array

instance [ToData α] : ToData (Array α) where
  toData uuids a := return Data.arr (← a.mapM (toData uuids))

instance [ToMrdiType α] [Inhabited α] : ToMrdiType (Array α) :=
  ⟨fun uuids _ => return MrdiType.obj "Vector" $ Mrdi.TypeToData $ ← toMrdiType uuids (default : α)⟩

instance [ToRefs α] [Inhabited α] : ToRefs $ Array α where
  toRefs uuids a := toRefs uuids a[0]!

end Array

section List

instance [ToData α] : ToData (List α) where
  toData uuids l := return Data.arr ⟨← l.mapM (toData uuids)⟩

instance [ToMrdiType α] [Inhabited α] : ToMrdiType (List α) :=
  ⟨fun uuids l => toMrdiType uuids (⟨l⟩ : Array α)⟩

instance [ToRefs α] [Inhabited α] : ToRefs $ List α where
  toRefs uuids l := toRefs uuids (⟨l⟩ : Array α)

end List

section Vector

instance [ToData α] : ToData (Vector α n) where
  toData uuids v := toData uuids v.val

instance [ToMrdiType α] [Inhabited α] : ToMrdiType (Vector α n) :=
  ⟨fun uuids v => toMrdiType uuids v.val⟩

instance [ToRefs α] [Inhabited α] : ToRefs $ Vector α n where
  toRefs uuids v := toRefs uuids v.val

end Vector

section Rat

instance : ToData ℚ where
  toData _ q := return Data.str s!"{q.num}//{q.den}"

instance : ToMrdiType ℚ := ⟨fun _ _ => return MrdiType.str "QQFieldElem"⟩

instance : ToData $ TypeWrapper ℚ := ⟨fun _ _ => return Mrdi.Data.str "QQField"⟩

end Rat

section Int

instance : ToMrdiType Int := ⟨fun _ _ => return MrdiType.str "Base.Int"⟩

instance : ToData $ TypeWrapper Int := ⟨fun _ _ => return Mrdi.Data.str "ZZRing"⟩

end Int

section Nat

instance : ToMrdiType ℕ := ⟨fun _ _ => return MrdiType.str "Base.Int"⟩

-- TODO should it be send to unsigned int instead?
instance : ToData $ TypeWrapper Nat := ⟨fun _ _ => return Mrdi.Data.str "ZZRing"⟩

end Nat

section Fin

instance : ToMrdiType (Fin n) := ⟨fun uuids n => toMrdiType uuids n.val⟩

-- TODO should it be send to unsigned int instead?
instance : ToData $ TypeWrapper $ Fin n := ⟨fun _ _ => return Mrdi.Data.str "ZZRing"⟩

instance : ToData $ Fin n := ⟨fun uuids n  => toData uuids n.val⟩

end Fin

section String

instance : ToMrdiType String := ⟨fun _ _ => return MrdiType.str "String"⟩

end String

section Bool

instance : ToMrdiType Bool := ⟨fun _ _ => return MrdiType.str "Bool"⟩

end Bool

section Polynom

/- {
  "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","0.13.0"]},
  "_type":{"name":"PolyRingElem","params":"07a275fe-045f-4551-ad07-a805bf7896a1"},
  "data":[["0","1"],["1","-1"],["2","3"]],
  "_refs":{
    "07a275fe-045f-4551-ad07-a805bf7896a1":{
      "_type":"PolyRing",
      "data":{"base_ring":{"_type":"QQField"},
      "symbols":["x"]}
    }
  }
} -/

instance [Semiring R] : ToMrdiType $ TypeWrapper $ Polynomial R := ⟨fun _ _ => return MrdiType.str "PolyRing"⟩

instance [Semiring R] [ToData (TypeWrapper R)] : ToData $ TypeWrapper (Polynomial R) where
  toData uuids _ :=
    return Mrdi.Data.mkObj
      [("basering", Mrdi.Data.mkObj [("_type", ← toData uuids (default : TypeWrapper R))]),
        ("symbols", Mrdi.Data.arr #[Mrdi.Data.str "x"])]

instance [Semiring R] : ToMrdiType (Polynomial R) where
  toMrdiType uuids _ := return MrdiType.obj "PolyRingElem" (Data.str $ toString uuids[0]!)

-- TODO seems to be noncomputable. Is there a way to go through the support?
instance [Semiring R] : ToData (Polynomial R) where
  toData _ _ := throwError "ToData Polynomials is not implemented yet" --[[n, p.coeff n] for n in p.support]

instance [Semiring R] [ToData (TypeWrapper R)] : ToRefs $ (Polynomial R) where
  toRefs uuids p := return mkRefs [(uuids[0]!, ← toRef uuids p)]

end Polynom

section Permutation

-- TODO use FinEnum instead of Fin n

/- {
"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
"_type":"PermGroup",
"data":{"degree":"5","gens":[["2","3","4","5","1"],["2","1"]]},
"id":"8a381e0b-de9d-4461-9f0f-ab078a664955"
} -/

instance : ToMrdiType $ TypeWrapper $ Equiv.Perm (Fin n) := ⟨fun _ _ => return MrdiType.str "PermGroup"⟩

-- For Example:
-- "data":{"degree":"5","gens":[["2","3","4","5","1"],["2","1"]]}
instance : ToData $ TypeWrapper $ Equiv.Perm (Fin n) where
  toData _ _ := return Data.mkObj [("degree", Data.str $ toString n),
    -- S(n) is generated by (2, 1) and (2, ..., n, 1)
    ("gens", Data.arr #[Data.arr ⟨List.rotate (List.map (Data.str $ toString ·) $ List.range' 1 n) 1⟩,
      Data.arr #[Data.str "2", Data.str "1"]])]

instance : ToRef $ Equiv.Perm (Fin n) where
  toRef _ p := return mk none (← toMrdiType [] (get_t p)) (← toData [] (get_t p)) none none

/- {
    "_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.0-DEV-fbd34b88fbedbbcb729a1e2ea5037b1860cda204"]},
    "_type":{"name":"PermGroupElem","params":"880c22b1-491b-482b-b98e-987d6ebdd940"},
    "data":["2","3","1","5","4"],
    "_refs":{"880c22b1-491b-482b-b98e-987d6ebdd940":{
        "_type":"PermGroup",
        "data":{"degree":"5","gens":[["2","3","4","5","1"],["2","1"]]}
        }
    }
} -/

instance : ToData $ Equiv.Perm (Fin (n + 1)) where
  toData _ p := do
    let mut a : List ℕ := []
    -- TODO there should be a definition for the for loop in mathlib.
    -- We want to know for every element in `Fin n` where p sends it to
    -- maybe its better to use FinEnum for the for loop
    for i in (List.range (n + 1)).reverse do
      a := (p.toFun i) :: a
    return PlusOneShift $ Data.arr (⟨a.map (Data.str $ toString ·)⟩)
    --"data":["2","3","1","5","4"]

instance : ToMrdiType $ Equiv.Perm (Fin n) where
  toMrdiType uuids _ := return MrdiType.obj "PermGroupElem" (Data.str $ toString uuids[0]!)

instance : ToRefs $ Equiv.Perm (Fin (n + 1)) where
  toRefs uuids p := return mkRefs [(uuids[1]!, ← toRef uuids p)]

end Permutation

section FreeGroup

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

instance : ToMrdiType $ TypeWrapper $ FreeGroup α where
  toMrdiType _ _ := return MrdiType.str "FPGroup"

-- TODO do we need to specify everything?
instance [Fintype α] : ToData $ TypeWrapper $ FreeGroup α where
  toData _ _ := do
    let names := Data.arr ⟨List.map (Mrdi.Data.str s!"x{· + 1}") (List.range (Fintype.card α))⟩
    let x := Data.mkObj [("GapType", Data.str "IsFreeGroup"), ("wfilt", Data.str "IsLetterWordsFamily"), ("names", names)]
    return Data.mkObj [("X", x)]

-- the first uuid should be a reference to the free group
instance : ToMrdiType $ FreeGroup α where
  toMrdiType uuids _ := return MrdiType.obj "FPGroupElem" (Mrdi.Data.str (toString uuids[1]!))

-- convert a Bool to a Int, false -> -1, true -> 1
private def Bool.isInvToInt : Bool → Int
  | false => -1
  | true => 1

-- convert [(a1, b1), (a2, b2), ...] to [a1, b1, a2, b2]
private def List.flat {α} : List (α × α) → List α
  | [] => []
  | (a₁, a₂) :: as => a₁ :: a₂ :: flat as

instance [FinEnum α] : ToData $ FreeGroup α where
  toData _ g := Id.run <| do
    let word : List (α × Bool) := FreeGroup.toWord g
    -- +1 cause GAP starts counting at 1
    let word_Int : List (Int × Int) := word.map (fun (a, b) => ((FinEnum.equiv.toFun a : ℕ) + 1, Bool.isInvToInt b))
    toData [] (List.flat word_Int)

instance [Fintype α] : ToRef $ FreeGroup α where
  toRef _ g := return mk none (← toMrdiType [] (get_t g)) (← toData [] (get_t g)) none none

instance [Fintype α] : ToRefs $ FreeGroup α where
  toRefs uuids g := return mkRefs [(uuids[1]!, ← toRef uuids g)]

end FreeGroup

section PresentedGroup

/- Presented Group uses a Set of relations, which is noncomputable. -/

instance : ToMrdiType $ TypeWrapper $ FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels) where
  toMrdiType _ _ := return MrdiType.str "FPGroup"

/-- uuids[0] should be the uuid for the free group -/
instance [FinEnum α] : ToData $ TypeWrapper $ FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels) where
  toData uuids _ := do
    let x := Data.mkObj
      [("GapType", Data.str "IsSubgroupFpGroup"), ("freeGroup", Data.str (toString uuids[1]!)), ("relators", ← toData uuids rels)]
    return Data.mkObj [("X", x)]

instance [Fintype α] : ToRefs $ TypeWrapper $ FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels) where
  toRefs uuids _ := return mkRefs [(uuids[1]!, ← toRef uuids (default : FreeGroup α))]

/- TODO delete this instance. it's for debugging -/
instance [FinEnum α] : ToMrdi $ FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels) where
  toMrdi uuids g := toMrdi (α := TypeWrapper $ FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels)) uuids (get_t g)

instance [FinEnum α] {rels : List (FreeGroup α)} : ToMrdi $ PresentedGroup (List.toSet rels) where
  toMrdi uuids g := toMrdi (α := FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels)) uuids g

end PresentedGroup

section Matrix

-- TODO why can't I use a simple nested for loop? leeds to creepy errors.
instance [ToData α] : ToData $ Matrix (Fin (m + 1)) (Fin (n + 1)) α where
  toData uuids A := do
    let get_row : Fin (m + 1) → List α := fun i : Fin (m + 1) => Id.run <| do
      let mut row : List α := []
      for j in (List.range (n + 1)).reverse do
        let aij : α := A (Fin.ofNat i) (Fin.ofNat j)
        row := aij :: row
      return row
    let matrix : List (List α) := Id.run <| do
      let mut rows : List (List α) := []
      for i in (List.range (m + 1)).reverse do
        let row : List α := get_row i
        rows := row :: rows
      return rows
    toData uuids matrix

instance [ToMrdiType α] [Inhabited α] : ToMrdiType $ Matrix (Fin m) (Fin n) α where
  toMrdiType uuids _ := return MrdiType.obj "Matrix" $ Mrdi.TypeToData $ ← toMrdiType uuids (default : α)

end Matrix

end Mrdi
