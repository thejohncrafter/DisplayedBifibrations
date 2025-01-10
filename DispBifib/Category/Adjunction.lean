import DispBifib.Notation

import DispBifib.Category.Category
import DispBifib.Category.Functor

namespace DispBifib

structure Adjunction
  {C D : Category.{u,v}} (L : C ⇒ D) (R : D ⇒ C)
where
  appₗᵣ
    : {c : C} → {d : D}
    → (L c ⟶ d) → (c ⟶ R d)
  appᵣₗ
    : {c : C} → {d : D}
    → (c ⟶ R d) → (L c ⟶ d)
  naturality₁ :
    ∀ {c₁ c₂ : C} (f : c₂ ⟶ c₁),
    ∀ {d},
    ∀ (φ : L c₁ ⟶ d),
      appₗᵣ (L.fmap f ≫ φ) = f ≫ appₗᵣ φ
  naturality₂ :
    ∀ {c},
    ∀ {d₁ d₂ : D} (g : d₁ ⟶ d₂),
    ∀ (φ : L c ⟶ d₁),
      appₗᵣ (φ ≫ g) = appₗᵣ φ ≫ R.fmap g
  naturality₃ :
    ∀ {c₁ c₂ : C} (f : c₂ ⟶ c₁),
    ∀ {d},
    ∀ (φ : c₁ ⟶ R d),
      appᵣₗ (f ≫ φ) = L.fmap f ≫ appᵣₗ φ
  naturality₄ :
    ∀ {c},
    ∀ {d₁ d₂ : D} (g : d₁ ⟶ d₂),
    ∀ (φ : c ⟶ R d₁),
      appᵣₗ (φ ≫ R.fmap g) = appᵣₗ φ ≫ g

end DispBifib
