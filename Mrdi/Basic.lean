import Mathlib
import Mrdi.RBNode
import Mrdi.UUID
import Mrdi.ToExpr

/- In this File we define `Mrdi`. It represents data in the Mrdi format, which is JSON with a certain JSON schema.
  It is used for serialization by the julia library Oscar and is designed to save diverse mathematical objects.
  We use it to send data back and forth between Lean and julia.
  Each Mrdi object has a type and can have a namespace (ns), data, references (refs) and an id.
  For more details I would refer to the paper
  https://arxiv.org/abs/2309.00465#:~:text=We%20describe%20a%20generic%20JSON,used%20in%20a%20different%20context.

  This file consists also of some definions necessary to define `Mrdi` and some basic tools, theorems and instances.
-/

-- TODO
-- We copy and duplicate a lot of code from Json. Is it possible to cleanly generalize it?
-- If Json switches to RBMap, so should Mrdi

open Qq Lean Json

/-- The namespace of an mrdi object. It should contain information about the system in which it was defined.
   For example: "Oscar", url for Oscar, version -/
structure Mrdi.Ns : Type where
  json : Json
  deriving Inhabited, ToExpr

namespace Mrdi

instance : ToJson Ns := ⟨fun ns => ns.json⟩

instance : FromJson Ns := ⟨fun j => pure ⟨j⟩⟩

-- TODO this should probably be {"_ns": {"Lean", ["some github", "version"]}}
-- else it should be the latest tested oscar version for which everything works
def oscarNs : Ns := ⟨mkObj [("Oscar", Json.arr #[Json.str "https://github.com/oscar-system/Oscar.jl", Json.str "0.13.0"])]⟩

/-- The data of an mrdi object -/
protected inductive Data
  | str (s : String)
  | arr (a : Array Mrdi.Data)
  -- following the style of Json:
  -- uses RBNode instead of RBMap because RBMap is a def
  -- and thus currently cannot be used to define a type that
  -- is recursive in one of its parameters
  --
  -- the key should only consist of lower letters (a-z)
  | obj (kvPairs : RBNode String fun _ => Mrdi.Data)
  deriving Inhabited, BEq, ToExpr

namespace Data

/-- For debugging -/
partial def DataToString : Mrdi.Data → String
  | str s => s!"str {s}"
  | arr a => match a.data with
      | [] => "[]"
      | (a :: as) => DataToString a ++ " :: " ++ DataToString (arr ⟨as⟩)
  | obj _ => "obj"

instance : ToString Mrdi.Data := ⟨DataToString⟩

/-- the key should only consist of lower letters (a-z) -/
def isValidKey (s : String) : Bool := s.all Char.isLower

-- temporary ugliness until we can use RBMap for Mrdi.Data objects, see Json
def mkObj (o : List (String × Mrdi.Data)) : Mrdi.Data :=
  obj <| Id.run do
    let mut kvPairs := RBNode.leaf
    for ⟨k, v⟩ in o do
      kvPairs := kvPairs.insert compare k v
    kvPairs

-- TODO show termination
def map (f : String → String) : Mrdi.Data → Mrdi.Data
  | str s => str (f s)
  | arr a => arr $ a.map (map f)
  | obj o => obj $ o.map (fun _ => map f)
termination_by sizeOf (α := Mrdi.Data)
decreasing_by
  all_goals simp
  sorry
  sorry

private partial def toJson' : Mrdi.Data → Json
  | Mrdi.Data.str s => Json.str s
  | Mrdi.Data.arr a =>
      let _ : ToJson Mrdi.Data := ⟨toJson'⟩
      Json.arr (a.map toJson)
  | Mrdi.Data.obj kvs =>
      let _ : ToJson Mrdi.Data := ⟨toJson'⟩
      Json.obj (kvs.map (fun _ => toJson))

instance : ToJson Mrdi.Data := ⟨toJson'⟩

private partial def fromJson?' : Json → Except String Mrdi.Data
  | Json.str s => return Mrdi.Data.str s
  | Json.arr a => do
      let _ : FromJson Mrdi.Data := ⟨fromJson?'⟩
      return Mrdi.Data.arr (← a.mapM (fromJson? : Json → Except String Mrdi.Data))
  | Json.obj kvs => do
      let _ : FromJson Mrdi.Data := ⟨fromJson?'⟩
      return Mrdi.Data.obj (← kvs.mapM (fun _ => fromJson?))
  | _ => throw "expected string, array or object for data"

instance : FromJson Mrdi.Data := ⟨fromJson?'⟩

def getStr? : Mrdi.Data → Except String String
 | str s => return s
 | _ => throw "data string expected"

def getObj? : Mrdi.Data → Except String (RBNode String (fun _ => Mrdi.Data))
  | obj kvs => return kvs
  | _       => throw "data object expected"

def getArr? : Mrdi.Data → Except String (Array Mrdi.Data)
  | arr a => return a
  | _     => throw "data array expected"

def getObjVal? : Mrdi.Data → String → Except String Mrdi.Data
  | obj kvs, k =>
    match kvs.find compare k with
    | some v => return v
    | none => throw s!"property not found: {k}"
  | _      , _ => throw "data object expected"

def getArrVal? : Mrdi.Data → Nat → Except String Mrdi.Data
  | arr a, i =>
    match a.get? i with
    | some v => return v
    | none => throw s!"index out of bounds: {i}"
  | _    , _ => throw "data array expected"

def setObjVal! : Mrdi.Data → String → Mrdi.Data → Mrdi.Data
  | obj kvs, k, v => bif isValidKey k
                     then obj <| kvs.insert compare k v
                     else panic! s!"The key {k} should consist of only lower letters!"
  | _      , _, _ => panic! "Mrdi.Data.setObjVal!: not an object"

end Data

-- we can't call it `Mrdi.Type` as this might lead to confusion with `Type`
/-- The type of an mrdi object. It tells us what kind of object it is -/
inductive MrdiType
  | str (s : String)
  | obj (name : Option String) (params : Option Mrdi.Data)
  deriving Inhabited, BEq, ToExpr

namespace MrdiType

def getStr? : MrdiType → Except String String
 | str s => return s
 | _ => throw "String expected for MrdiType"

def getName? : MrdiType → Except String (Option String)
  | obj name _ => return name
  | _       => throw "object expected for name"

def getName! (type : MrdiType) : Except String String := do
  let some name ← getName? type | throw "name is none"
  return name

def getParams? : MrdiType → Except String (Option Mrdi.Data)
  | obj _ data => return data
  | _       => throw "object expected for params"

def getParams! (type : MrdiType) : Except String Mrdi.Data := do
  let some params ← getParams? type | throw "params is none"
  return params

instance : ToJson MrdiType where
  toJson
    | str s => Json.str s
    | obj none        none          => null
    | obj none        (some params) => mkObj [("params", toJson params)]
    | obj (some name) none          => mkObj [("name", toJson name)]
    | obj (some name) (some params) => mkObj [("name", toJson name), ("params", toJson params)]

instance : FromJson MrdiType where
  fromJson?
    | Json.str s => return MrdiType.str s
    | Json.obj kvs => do
        let name := ((← (Json.obj kvs).getObjVal? "name").getStr?).toOption
        let params := (fromJson? (← ((Json.obj kvs).getObjVal? "params"))).toOption
        return MrdiType.obj name params
    | _ => throw "string or object for MrdiType expected"

end MrdiType

end Mrdi

inductive Mrdi
  | mk (ns : Option Mrdi.Ns) (type : Mrdi.MrdiType) (data : Option Mrdi.Data)
      (refs : Option (RBNode UUID fun _ => Mrdi)) (id : Option UUID)
  deriving Inhabited, ToExpr

namespace Mrdi

/-- The namespace of an mrdi object. It should contain information about the system in which it was defined.
   For example: "Oscar", url for Oscar, version -/
def ns : Mrdi → Option Ns
  | mk ns _ _ _ _ => ns

/-- The type of an mrdi object. It tells us what kind of object it is -/
def type : Mrdi → Mrdi.MrdiType
  | mk _ t _ _ _ => t

/-- The data of an mrdi object -/
def data : Mrdi → Option Mrdi.Data
  | mk _ _ d _ _ => d

/-- The data of an mrdi object -/
def data! : Mrdi → Except String Mrdi.Data
  | mk _ _ none     _ _ => throw "no data"
  | mk _ _ (some d) _ _ => pure d

/-- The references of an mrdi object. They are mrdi objects themself.
   For example a matrix needs to know the type of its elements. -/
def refs : Mrdi → Option (RBNode UUID fun _ => Mrdi)
  | mk _ _ _ r _ => r

/-- The reference of an mrdi object belonging to the key -/
def ref : Mrdi → UUID → Option Mrdi
  | mk _ _ _ none               _, _    => none
  | mk _ _ _ (some RBNode.leaf) _, _    => none
  | mk _ _ _ (some r)           _, uuid => Lean.RBNode.find compare r uuid

/-- The id of an mrdi object. Other mrdi objects can refer to this object using the id. -/
protected def id : Mrdi → Option UUID
  | mk _ _ _ _ uuid => uuid

def hasNs (mrdi : Mrdi) : Bool := Option.isSome $ mrdi.ns

def hasData (mrdi : Mrdi) : Bool := Option.isSome $ mrdi.data

def hasRefs (mrdi : Mrdi) : Bool := Option.isSome $ mrdi.refs

def hasId (mrdi : Mrdi) : Bool := Option.isSome $ mrdi.id

def setId (id : UUID) : Mrdi → Mrdi
  | mk ns type data refs _ => mk ns type data refs id

def mkRefs (o : List (UUID × Mrdi)) : RBNode UUID fun _ => Mrdi := Id.run do
  let mut kvPairs := RBNode.leaf
  for ⟨k, v⟩ in o do
    kvPairs := kvPairs.insert compare k v
  kvPairs

def appendRefs (ref₁ ref₂ : RBNode UUID fun _ => Mrdi) : RBNode UUID fun _ => Mrdi :=
  RBNode.appendTrees ref₁ ref₂

def TypeToData : MrdiType → Mrdi.Data
  | MrdiType.str s => Mrdi.Data.str s
  | MrdiType.obj name? params? => Id.run do
      let mut fields := ([] : List (String × Mrdi.Data))
      if name?.isSome then
        let some name := name? | unreachable!
        fields := ("name", Mrdi.Data.str name) :: fields
      if params?.isSome then
        let some params := params? | unreachable!
        fields := ("params", params) :: fields
      Mrdi.Data.mkObj fields

/-- Checks if all components except `ns` and `id` are equal -/
private partial def beq' : Mrdi → Mrdi → Bool
  | mk _ type₁ data₁ none         _, mk _ type₂ data₂ none         _ => type₁ == type₂ && data₁ == data₂
  | mk _ _     _     none         _, mk _ _     _     _            _ => false
  | mk _ _     _     _            _, mk _ _     _     none         _ => false
  | mk _ type₁ data₁ (some refs₁) _, mk _ type₂ data₂ (some refs₂) _ =>
      let _ : BEq Mrdi := ⟨beq'⟩
      let szR₁ := refs₁.fold (init := 0) (fun a _ _ => a + 1)
      let szR₂ := refs₂.fold (init := 0) (fun a _ _ => a + 1)
      type₁ == type₂
        && data₁ == data₂
        && szR₁ == szR₂
        && refs₁.all fun uuid f₁ =>
          match refs₂.find compare uuid with
          | none    => false
          | some f₂ => f₁ == f₂

instance : BEq Mrdi := ⟨beq'⟩

private partial def fromJson?' (j : Json) : Except String Mrdi := do
  let ns : Option Ns := (fromJson? $ j.getObjValD "_ns").toOption
  let id : Option UUID := (j.getObjVal? "id" >>= Json.getStr? >>= UUID.parse).toOption
  let type : Mrdi.MrdiType ← fromJson? (← j.getObjVal? "_type")
  let data : Option Mrdi.Data := (fromJson? (j.getObjValD "data")).toOption
  let _ : FromJson Mrdi := ⟨fromJson?'⟩
  match (getObj? (j.getObjValD "_refs")) with
  | .ok json_refs => do
      let refs ← (RBNode.mapM' UUID.parse (fun _ => (fromJson? : Json → Except String Mrdi))) json_refs
      return Mrdi.mk ns type data refs id
  | .error _ => return Mrdi.mk ns type data none id

instance : FromJson Mrdi := ⟨fromJson?'⟩

private partial def toJson' (mrdi : Mrdi) : Json := Id.run <| do
  let mut kvPairs := ([] : List (String × Json))
  if mrdi.hasNs then kvPairs := ("_ns", toJson mrdi.ns) :: kvPairs
  if mrdi.hasId then kvPairs := ("id", Json.str $ toString $ ((mrdi.id).getD default)) :: kvPairs
  kvPairs := ("_type", toJson mrdi.type) :: kvPairs
  if mrdi.hasData then kvPairs := ("data", toJson mrdi.data) :: kvPairs
  let _ : ToJson Mrdi := ⟨toJson'⟩
  if mrdi.hasRefs then kvPairs := ("_refs", toJson mrdi.refs) :: kvPairs
  return mkObj kvPairs

instance : ToJson Mrdi := ⟨toJson'⟩

instance : ToString Mrdi := ⟨fun mrdi => toString (toJson mrdi)⟩

instance : ToFormat Mrdi := ⟨fun mrdi => format (toJson mrdi)⟩

def compress (mrdi : Mrdi) : String := Json.compress (toJson mrdi)

def parse (s : String) : Except String Mrdi := Json.parse s >>= fromJson?

end Mrdi
