import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed.DisplayedCategory
import DispBifib.Displayed.DisplayedFunctor

namespace DispBifib

protected def total_category
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀)
  : Category.{u,v}
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
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀)
  : ∫ C ⇒ C₀
where
  map | ⟨ a₀, _ ⟩ => a₀
  fmap | ⟨ f₀, _ ⟩ => f₀
  fmap_id _ := rfl
  fmap_comp _ _ := rfl

private theorem id_mul
  {C : Category.{u,v}} (x : C)
  : 𝟙 x ≫ 𝟙 x = 𝟙 x
:= C.comp_id _

def fiber
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀) (x : C₀)
  : Category.{u,v}
where
  obj := C x
  hom a b := a [ 𝟙 x ]⟶ b
  id a := 𝟙 a
  comp {a b c} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c) :=
    reindex (fun f₀ => a [ f₀ ]⟶ c) (id_mul x) (f ≫ g)
  id_comp {a b} f := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ b)
    apply IdxEq.reindexₗ (id_mul x)
    exact C.id_comp _
  comp_id {a b} f := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ b)
    apply IdxEq.reindexₗ (id_mul x)
    exact C.comp_id _
  assoc {a b c d} (f : a [ 𝟙 x ]⟶ b) (g : b [ 𝟙 x ]⟶ c) (h : c [ 𝟙 x ]⟶ d) := by
    apply eq_of_idx_eq (fun f₀ => a [ f₀ ]⟶ d)
    apply IdxEq.trans3 _ (C.assoc f g h) _
    . apply IdxEq.reindexₗ (id_mul x)
      apply idxCongrArg (fun {φ₀ : x ⟶ x} (φ : a [ φ₀ ]⟶ c) => φ ≫ h)
      apply IdxEq.reindexₗ (id_mul x)
      rfl
    . apply IdxEq.reindexᵣ (id_mul x)
      apply idxCongrArg (fun {φ₀ : x ⟶ x} (φ : b [ φ₀ ]⟶ d) => f ≫ φ)
      apply IdxEq.reindexᵣ (id_mul x)
      rfl

end DispBifib
