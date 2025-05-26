import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed.DisplayedCategory
import DispBifib.Displayed.DisplayedFunctor

namespace DispBifib

protected def total_category
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀)
  : Category (max u u') (max v v')
where
  obj := (a₀ : C₀) × (C a₀)
  hom | ⟨ a₀, a ⟩, ⟨ b₀, b ⟩ => (f₀ : a₀ ⟶ b₀) × (a [ f₀ ]⟶ b)
  id | ⟨ a₀, a ⟩ => ⟨ 𝟙 a₀, 𝟙 a ⟩
  comp | ⟨ f₀, f ⟩, ⟨ g₀, g ⟩ => ⟨ f₀ ≫ g₀, f ≫ g ⟩
  id_comp _ := by
    apply sigma_eq_of_idx_eq
    exact C.id_comp _
  comp_id _ := by
    apply sigma_eq_of_idx_eq
    exact C.comp_id _
  assoc _ _ _ := by
    apply sigma_eq_of_idx_eq
    exact C.assoc _ _ _

notation "∫ " C:max => DispBifib.total_category C

def display_map
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀)
  : ∫ C ⇒ C₀
where
  map | ⟨ a₀, _ ⟩ => a₀
  fmap | ⟨ f₀, _ ⟩ => f₀
  fmap_id _ := rfl
  fmap_comp _ _ := rfl

private theorem id_mul
  {C : Category u v} (x : C)
  : 𝟙 x ≫ 𝟙 x = 𝟙 x
:= C.comp_id _

def fiber_comp
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀} {x : C₀}
  {a b c : C x} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c)
  : a [ 𝟙 x ]⟶ c
:= reindex (fun f₀ => a [ f₀ ]⟶ c) (id_mul x) (f ≫ g)

def fiber_comp_eq
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀} {x : C₀}
  {a b c : C x} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c)
  : fiber_comp f g =* f ≫ g
:= IdxEq.reindexₗ (id_mul x) (IdxEq.refl _)

def fiber
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀) (x : C₀)
  : Category u' v'
where
  obj := C x
  hom a b := a [ 𝟙 x ]⟶ b
  id a := 𝟙 a
  comp := fiber_comp
  id_comp {a b} f := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ b)
    apply IdxEq.trans (fiber_comp_eq _ _)
    exact C.id_comp _
  comp_id {a b} f := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ b)
    apply IdxEq.trans (fiber_comp_eq _ _)
    exact C.comp_id _
  assoc {a b c d} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c) (h : c [ 𝟙 x ]⟶ d) := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ d)
    apply IdxEq.trans3 _ (C.assoc f g h) _
    . apply IdxEq.trans (fiber_comp_eq _ _)
      apply idxeq_comp
      apply IdxEq.trans (fiber_comp_eq _ _)
      rfl
    . apply IdxEq.trans _ (fiber_comp_eq _ _).symm
      apply comp_idxeq
      apply IdxEq.trans _ (fiber_comp_eq _ _).symm
      rfl

def fiber_magma
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀) (x : C₀)
  : Magma u' v'
where
  obj := C x
  hom a b := a [ 𝟙 x ]⟶ b
  id a := 𝟙 a
  comp {a b c} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c) :=
    reindex (fun f₀ => a [ f₀ ]⟶ c) (id_mul x) (f ≫ g)

end DispBifib
