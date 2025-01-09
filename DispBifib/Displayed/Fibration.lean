import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed.DisplayedCategory
import DispBifib.Displayed.DisplayedFunctor
import DispBifib.Displayed.Total

namespace DispBifib

structure Cartesian
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {a₀ b₀ : C₀} {a : C a₀} {b : C b₀}
  {f₀ : a₀ ⟶ b₀} (f : a [ f₀ ]⟶ b)
where
  lift
    : {c₀ : C₀} → {c : C c₀}
    → {g₀ : c₀ ⟶ b₀} → (g : c [ g₀ ]⟶ b)
    → (w₀ : c₀ ⟶ a₀)
    → w₀ ≫ f₀ = g₀
    → (c [ w₀ ]⟶ a)
  lift_def :
    ∀ {c₀ : C₀} {c : C c₀},
    ∀ {g₀ : c₀ ⟶ b₀} (g : c [ g₀ ]⟶ b),
    ∀ (w₀ : c₀ ⟶ a₀),
      (h : w₀ ≫ f₀ = g₀) → lift g w₀ h ≫ f =* g
  lift_unique :
    ∀ {g₀ : c₀ ⟶ b₀} (g : c [ g₀ ]⟶ b),
    ∀ (w₀ : c₀ ⟶ a₀), (h : w₀ ≫ f₀ = g₀) →
    ∀ (w' : c [ w₀ ]⟶ a),
      w' ≫ f =* g → w' = lift g w₀ h

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

end DispBifib
