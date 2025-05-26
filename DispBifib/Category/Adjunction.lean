import DispBifib.Notation

import DispBifib.Category.Category
import DispBifib.Category.Functor

namespace DispBifib

class Adjunction
  {C D : Category u v} (L : C ⇒ D) (R : D ⇒ C)
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

infix:15 " ⊣ " => Adjunction

def Adjunction.unit
  {C D : Category u v} (L : C ⇒ D) (R : D ⇒ C) [adj : L ⊣ R]
  : 𝟙 C ⟶ L ≫ R
where
  app a := adj.appₗᵣ (𝟙 (L a))
  naturality {a b} f := by
    show f ≫ appₗᵣ (𝟙 (L b)) = appₗᵣ (𝟙 (L a)) ≫ R.fmap (L.fmap f)
    rw [← adj.naturality₁, ← adj.naturality₂]
    rw [D.comp_id, D.id_comp]

def Adjunction.counit
  {C D : Category u v} (L : C ⇒ D) (R : D ⇒ C) [adj : L ⊣ R]
  : R ≫ L ⟶ 𝟙 D
where
  app a := adj.appᵣₗ (𝟙 (R a))
  naturality {a b} f := by
    show L.fmap (R.fmap f) ≫ appᵣₗ (𝟙 (R b)) = appᵣₗ (𝟙 (R a)) ≫ f
    rw [← adj.naturality₃, ← adj.naturality₄]
    rw [C.comp_id, C.id_comp]

end DispBifib
