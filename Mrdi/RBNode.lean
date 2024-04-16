import Lean.Data.Json
import Lean.Expr
import Mathlib.Tactic.ToExpr

/- This file contains additional definitions and instances for `RBNode` which I need for the project. -/

-- TODO check what should be added to Mathlib

section ToExprRBNode

open Lean Json

deriving instance ToExpr for RBColor

private def RBNodeExpr {α : Type u} {β : Type v} [ToExpr α] [ToExpr β] [ToLevel.{u}] [ToLevel.{v}]
  : RBNode α (fun _ => β) → Expr
  | RBNode.leaf => mkApp2 (mkConst ``RBNode.leaf [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
      (toTypeExpr α) (.lam default (toTypeExpr α) (toTypeExpr β) .default)
  | RBNode.node color lchild key val rchild =>
      mkApp7 (mkConst ``RBNode.node [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
        (toTypeExpr α) (.lam default (toTypeExpr α) (toTypeExpr β) .default)
        (toExpr color) (RBNodeExpr lchild) (toExpr key) (toExpr val) (RBNodeExpr rchild)

instance {α : Type u} {β : Type v} [ToExpr α] [ToExpr β] [ToLevel.{u}] [ToLevel.{v}] : ToExpr (RBNode α (fun _ => β)) where
  toExpr r := RBNodeExpr (α := α) r
  toTypeExpr := mkApp2 (mkConst ``RBNode [ToLevel.toLevel.{u}, ToLevel.toLevel.{v}])
    (toTypeExpr α) (.lam default (toTypeExpr α) (toTypeExpr β) .default)

end ToExprRBNode


section BEqRBNode

open Lean

def beq' {α : Type u} {β : Type v} [BEq β] [Ord α] (a₁ a₂ : RBNode α (fun _ => β)) : Bool :=
  let szA₁ := a₁.fold (init := 0) (fun a _ _ => a + 1)
  let szA₂ := a₂.fold (init := 0) (fun a _ _ => a + 1)
  szA₁ == szA₂ && a₁.all fun field fa =>
    match a₂.find compare field with
    | none    => false
    | some fb => fa == fb

instance {α : Type u} {β : Type v} [BEq β] [Ord α] : BEq (RBNode α (fun _ => β)) where
  beq := beq'

end BEqRBNode


section ToJsonRBNode

open Lean Json

private def toJson' {α : Type u} {β : Type v} [ToString α] [ToJson β] :
  RBNode α (fun _ => β) → RBNode String (fun _ => Json)
    | RBNode.leaf => RBNode.leaf
    | RBNode.node color lchild key val rchild =>
        RBNode.node color (toJson' lchild) (toString key) (toJson val) (toJson' rchild)

instance {α : Type u} {β : Type v} [ToString α] [ToJson β] : ToJson (RBNode α (fun _ => β)) where
  toJson j := obj (toJson' j)

end ToJsonRBNode


namespace Lean.RBNode

/-- a map function which can change keys and values -/
def map' {α : Type u} {δ : Type w} {β : α → Type v} {γ : δ → Type w}
  (g : α → δ) (f : (a : α) → β a → γ (g a))
  : RBNode α β → RBNode δ γ
  | leaf => leaf
  | node color lchild key val rchild => node color (lchild.map' g f) (g key) (f key val) (rchild.map' g f)

-- TODO: this version does what I need. Is it possible to let `γ` depend on `g a`?
--       Can we use two different Monads? And it should be possible to have some stuff have `Type w`
/-- a monadic map function which can change keys and values -/
def mapM' {M : Type v → Type v} [Applicative M] {α : Type u} {δ : Type v} {β : α → Type v} {γ : Type v}
  (g : α → M δ) (f : (a : α) → β a → M γ)
  : RBNode α β → M (RBNode δ (fun _ => γ))
  | leaf => pure leaf
  | node color lchild key val rchild =>
    pure (node color · · · ·) <*> lchild.mapM' g f <*> g key <*> f key val <*> rchild.mapM' g f

end Lean.RBNode
