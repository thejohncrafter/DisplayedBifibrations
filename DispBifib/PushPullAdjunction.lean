import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category
import DispBifib.Displayed

import DispBifib.Fibration
import DispBifib.Opfibration

namespace DispBifib

def push_pull_adjunction
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  [Fibration C] [Opfibration C]
  {x y : C₀} (f : x ⟶ y)
  : Adjunction (pushforward C f) (pullback C f)
where
  appₗᵣ {c : C x} {d : C y} (φ : (oplift_obj f c) [ 𝟙 y ]⟶ d) :=
    have p : 𝟙 x ≫ f = f ≫ 𝟙 y := by rw [C₀.id_comp, C₀.comp_id]
    bang f d (oplift_hom f c ≫ φ) (𝟙 x) p
  appᵣₗ {c : C x} {d : C y} (φ : c [𝟙 x ]⟶ lift_obj f d) :=
    have p : f ≫ 𝟙 y = 𝟙 x ≫ f := by rw [C₀.id_comp, C₀.comp_id]
    cobang f c (φ ≫ lift_hom f d) (𝟙 y) p
  naturality₁ {c₁ c₂} r {d} φ := by
    dsimp
    apply bang_unique
    apply IdxEq.trans3
      (idxeq_comp (fiber_comp_eq _ _) _)
      _
      (comp_idxeq _ (fiber_comp_eq _ _).symm)
    apply IdxEq.trans3 (C.assoc _ _ _) _ (C.assoc _ _ _)
    apply IdxEq.trans (comp_idxeq _ (bang_prop f _ _ _ _)) _
    apply IdxEq.trans (C.assoc _ _ _).symm
    apply idxeq_comp
    symm
    apply cobang_prop
  naturality₂ {c d₁ d₂} l φ := by
    dsimp
    apply bang_unique
    apply IdxEq.trans3
      (idxeq_comp (fiber_comp_eq _ _) _)
      _
      (comp_idxeq _ (fiber_comp_eq _ _).symm)
    apply IdxEq.trans3 (C.assoc _ _ _) _ (C.assoc _ _ _)
    apply IdxEq.trans (comp_idxeq _ (bang_prop f _ _ _ _)) _
    apply IdxEq.trans (C.assoc _ _ _).symm
    apply idxeq_comp
    apply bang_prop
  naturality₃ {c₁ c₂} r {d} φ := by
    dsimp
    apply cobang_unique
    apply IdxEq.trans3
      (comp_idxeq _ (fiber_comp_eq _ _))
      _
      (idxeq_comp (fiber_comp_eq _ _).symm _)
    apply IdxEq.trans3 (C.assoc _ _ _).symm _ (C.assoc _ _ _).symm
    apply IdxEq.trans (idxeq_comp (cobang_prop f _ _ _ _) _) _
    apply IdxEq.trans (C.assoc _ _ _)
    apply comp_idxeq
    apply cobang_prop
  naturality₄ {c d₁ d₂} l φ := by
    dsimp
    apply cobang_unique
    apply IdxEq.trans3
      (comp_idxeq _ (fiber_comp_eq _ _))
      _
      (idxeq_comp (fiber_comp_eq _ _).symm _)
    apply IdxEq.trans3 (C.assoc _ _ _).symm _ (C.assoc _ _ _).symm
    apply IdxEq.trans (idxeq_comp (cobang_prop f _ _ _ _) _) _
    apply IdxEq.trans (C.assoc _ _ _)
    apply comp_idxeq
    symm
    apply bang_prop

end DispBifib
