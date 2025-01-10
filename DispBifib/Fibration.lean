import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed

namespace DispBifib

structure Cartesian
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {a₀ b₀ : C₀} {a : C a₀} {b : C b₀}
  {f₀ : a₀ ⟶ b₀} (f : a [ f₀ ]⟶ b)
where
  bang
    : {c₀ : C₀} → {c : C c₀}
    → {g₀ : c₀ ⟶ b₀} → (g : c [ g₀ ]⟶ b)
    → (w₀ : c₀ ⟶ a₀)
    → w₀ ≫ f₀ = g₀
    → (c [ w₀ ]⟶ a)
  bang_prop :
    ∀ {c₀ : C₀} {c : C c₀},
    ∀ {g₀ : c₀ ⟶ b₀} (g : c [ g₀ ]⟶ b),
    ∀ (w₀ : c₀ ⟶ a₀),
      (h : w₀ ≫ f₀ = g₀) → bang g w₀ h ≫ f =* g
  bang_unique :
    ∀ {g₀ : c₀ ⟶ b₀} (g : c [ g₀ ]⟶ b),
    ∀ (w₀ : c₀ ⟶ a₀), (h : w₀ ≫ f₀ = g₀) →
    ∀ (w' : c [ w₀ ]⟶ a),
      w' ≫ f =* g → w' = bang g w₀ h

class Fibration
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀)
where
  cleavage_obj
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (b : C b₀)
    → C a₀
  cleavage_hom
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (b : C b₀)
    → ((cleavage_obj f₀ b) [ f₀ ]⟶ b)
  cleavage_prop
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (b : C b₀)
    → Cartesian (cleavage_hom f₀ b)

def lift_obj
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Fibration C]
  : {x y : C₀} → (f : x ⟶ y) → C y → C x
:= fib.cleavage_obj

def lift_hom
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Fibration C]
  : {x y : C₀} → (f : x ⟶ y) → (b : C y) → ((lift_obj f b) [ f ]⟶ b)
:= fib.cleavage_hom

def bang
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : c [ w₀ ]⟶ lift_obj f b
:= (fib.cleavage_prop f b).bang g w₀ h

def bang_prop
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : bang f b g w₀ h ≫ lift_hom f b =* g
:= (fib.cleavage_prop f b).bang_prop g w₀ h

def bang_unique
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : ∀ (w' : c [ w₀ ]⟶ lift_obj f b),
    (w' ≫ lift_hom f b =* g) → w' = bang f b g w₀ h
:= (fib.cleavage_prop f b).bang_unique g w₀ h

def pullback_functor
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀) [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) : fiber C y ⇒ fiber C x
where
  map b := lift_obj f b
  fmap {b b' : C y} (g : b [ 𝟙 y ]⟶ b') :=
    have p : 𝟙 x ≫ f = f ≫ 𝟙 y := by rw [C₀.id_comp, C₀.comp_id]
    bang f b' (lift_hom f b ≫ g) (𝟙 x) p
  fmap_id b := by
    symm
    apply bang_unique f b
    exact .trans (C.id_comp _) (C.comp_id _).symm
  fmap_comp {b₁ b₂ b₃} g g' := by
    dsimp
    symm
    apply bang_unique f b₃
    apply IdxEq.trans3
      (idxeq_comp (fiber_comp_eq _ _) _)
      _
      (comp_idxeq _ (fiber_comp_eq _ _).symm)
    apply IdxEq.trans3 (C.assoc _ _ _) _ (C.assoc _ _ _)
    apply IdxEq.trans (comp_idxeq _ (bang_prop f b₃ _ _ _)) _
    apply IdxEq.trans (C.assoc _ _ _).symm
    apply idxeq_comp (bang_prop _ _ _ _ _)


end DispBifib
