import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed

namespace DispBifib

structure Cocartesian
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {a₀ b₀ : C₀} {a : C a₀} {b : C b₀}
  {f₀ : a₀ ⟶ b₀} (f : a [ f₀ ]⟶ b)
where
  cobang
    : {c₀ : C₀} → {c : C c₀}
    → {g₀ : a₀ ⟶ c₀} → (g : a [ g₀ ]⟶ c)
    → (w₀ : b₀ ⟶ c₀)
    → f₀ ≫ w₀ = g₀
    → (b [ w₀ ]⟶ c)
  cobang_prop :
    ∀ {c₀ : C₀} {c : C c₀},
    ∀ {g₀ : a₀ ⟶ c₀} (g : a [ g₀ ]⟶ c),
    ∀ (w₀ : b₀ ⟶ c₀),
      (h : f₀ ≫ w₀ = g₀) → f ≫ cobang g w₀ h =* g
  cobang_unique :
    ∀ {g₀ : a₀ ⟶ c₀} (g : a [ g₀ ]⟶ c),
    ∀ (w₀ : b₀ ⟶ c₀), (h : f₀ ≫ w₀ = g₀) →
    ∀ (w' : b [ w₀ ]⟶ c),
      f ≫ w' =* g → w' = cobang g w₀ h

class Opfibration
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀)
where
  cleavage_obj
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (a : C a₀)
    → C b₀
  cleavage_hom
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (a : C a₀)
    → (a [ f₀ ]⟶ cleavage_obj f₀ a)
  cleavage_prop
    : {a₀ b₀ : C₀}
    → (f₀ : a₀ ⟶ b₀)
    → (a : C a₀)
    → Cocartesian (cleavage_hom f₀ a)

def oplift_obj
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  : {x y : C₀} → (f : x ⟶ y) → C x → C y
:= fib.cleavage_obj

def oplift_hom
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  : {x y : C₀} → (f : x ⟶ y) → (a : C x) → (a [ f ]⟶ oplift_obj f a)
:= fib.cleavage_hom

def cobang
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : (oplift_obj f a) [ w₀ ]⟶ c
:= (fib.cleavage_prop f a).cobang g w₀ h

def cobang_prop
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : oplift_hom f a ≫ cobang f a g w₀ h =* g
:= (fib.cleavage_prop f a).cobang_prop g w₀ h

def cobang_unique
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : ∀ (w' : (oplift_obj f a) [ w₀ ]⟶ c),
    (oplift_hom f a ≫ w' =* g) → w' = cobang f a g w₀ h
:= (fib.cleavage_prop f a).cobang_unique g w₀ h

def pushforward_functor
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀) [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) : fiber C x ⇒ fiber C y
where
  map a := oplift_obj f a
  fmap {a a' : C x} (g : a [ 𝟙 x ]⟶ a') :=
    have p : f ≫ 𝟙 y = 𝟙 x ≫ f := by rw [C₀.id_comp, C₀.comp_id]
    cobang f a (g ≫ oplift_hom f a') (𝟙 y) p
  fmap_id a := by
    symm
    apply cobang_unique f a
    exact .trans (C.comp_id _) (C.id_comp _).symm
  fmap_comp {a₁ a₂ a₃} g g' := by
    dsimp
    symm
    apply cobang_unique f a₁
    apply IdxEq.trans3
      (comp_idxeq _ (fiber_comp_eq _ _))
      _
      (idxeq_comp (fiber_comp_eq _ _).symm _)
    apply IdxEq.trans3 (C.assoc _ _ _).symm _ (C.assoc _ _ _).symm
    apply IdxEq.trans (idxeq_comp (cobang_prop f a₁ _ _ _) _) _
    apply IdxEq.trans (C.assoc _ _ _)
    apply comp_idxeq _ (cobang_prop _ _ _ _ _)

end DispBifib
