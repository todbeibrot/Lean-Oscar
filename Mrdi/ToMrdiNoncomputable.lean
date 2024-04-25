import Mrdi.ToMrdi
import Mrdi.Stream
import Qq

/-
This file contains functions to turn noncomputable objects into Mrdi. There can be no guarantee that
it works.
-/

-- like `Lean.Expr.app4?`
@[inline] def Lean.Expr.app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

namespace Mrdi

open Qq Lean Expr

/--
This works only if the set is defined by `Set.singleton` and `Set.insert`.
This is the case for sets defined by the syntax `{a, b, c}`.
-/
partial def Set.toList {u} {G : Q(Type u)} (S : Q(Set $G)) : MetaM Q(List $G) := do
  match S with
    | ~q(Set.singleton $a) =>
        return q([$a])
    | ~q(Set.insert $a $s) => do
        let as : Q(List $G) ← toList q($s)
        return q(($a) :: $as)
    | ~q(Insert.insert $a $s) => do
        let as : Q(List $G) ← toList q($s)
        return q(($a) :: $as)
    | ~q(Singleton.singleton $a) =>
        return q([$a])
    | e => do
        try
          let some (_, _, _, a, s) := app5? e ``Insert.insert | throwError "not an insert"
          let a : Q($G) := a
          let s : Q(Set $G) := s
          let as : Q(List $G) ← toList q($s)
          return q($a :: $as)
        catch _ => do
          let some (_, _, _, a) := app4? e ``Singleton.singleton | throwError s!"Set.toList failed to parse the set: {e}"
          let a : Q($G) := a
          return q([$a])

def toMrdiSet {u} {α : Q(Type $u)} (s : Q(Set $α)) (uuids : List UUID := []) : MetaM Mrdi := do
  let l ← Set.toList s
  IO.MrdiFile.Mrdi? l uuids

def ToMrdiMultiset {u} {α : Q(Type $u)} (s : Q(Multiset $α)) (uuids : List UUID := []) : MetaM Mrdi := do
  sorry

def ToMrdiFinset {u} {α : Q(Type $u)} (s : Q(Finset $α)) (uuids : List UUID := []) : MetaM Mrdi := do
  -- TODO test it. do we have to write the coercion out?
  let s : Q(Set $α) := s
  toMrdiSet s uuids

def ToMrdiFintype {u} {α : Q(Type $u)} (x : Q(Fintype $α)) (uuids : List UUID := []) : MetaM Mrdi := do
  ToMrdiFinset q(Fintype.elems (self := $x)) uuids

def ToMrdiPresentedGroup {u} {α : Q(Type $u)} {rels : Q(Set (FreeGroup $α))} (G : Q(PresentedGroup $rels)) (uuids : List UUID := []) :
  MetaM Mrdi := do
    sorry


end Mrdi
