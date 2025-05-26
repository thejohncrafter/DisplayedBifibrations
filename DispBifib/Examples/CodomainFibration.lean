import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category
import DispBifib.Displayed

import DispBifib.Fibration

import DispBifib.Examples.Pullbacks

namespace DispBifib

structure Arrow {C : Category u v} (cod : C) where
  dom : C
  φ : dom ⟶ cod

@[ext]
structure Square {C : Category u v}
  {a b : C} (f : Arrow a) (g : Arrow b)
  (φ : a ⟶ b)
where
  ψ : f.dom ⟶ g.dom
  coh : ψ ≫ g.φ = f.φ ≫ φ

theorem Square.eq {C : Category u v}
  {a b : C} {f : Arrow a} {g : Arrow b}
  {φ ψ : a ⟶ b} {F : Square f g φ} {G : Square f g ψ}
  (h₀ : φ = ψ)
  (h₁ : F.ψ = G.ψ)
  : F =* G
:= by
  subst h₀
  apply idx_eq_of_eq
  ext
  exact h₁

def codomain_displayed_category
  (C : Category u v)
  : DisplayedCategory (max u v) _ C
where
  obj d := Arrow d
  hom a b f := Square a b f
  id {a} | ⟨ a', f ⟩ => ⟨ 𝟙 a', by rw [C.id_comp, C.comp_id] ⟩
  comp {a b c a' b' c' f₀ g₀} f g :=
    ⟨ f.ψ ≫ g.ψ
    , by rw [C.assoc, g.coh, ← C.assoc, f.coh, C.assoc] ⟩
  id_comp f := by
    apply Square.eq
    . exact C.id_comp _
    . exact C.id_comp _
  comp_id f := by
    apply Square.eq
    . exact C.comp_id _
    . exact C.comp_id _
  assoc f g h := by
    apply Square.eq
    . exact C.assoc _ _ _
    . exact C.assoc _ _ _

set_option linter.unusedVariables false in
instance codomain_fibration
  (C : Category u v) [pb : Pullbacks C]
  : Fibration (codomain_displayed_category C)
where
  obj
  | sw, ⟨ se, ⟨ ne, e ⟩, s ⟩ =>
    ⟨ pb.obj ⟨ sw, se, ne, s, e ⟩, (pb.sol ⟨ sw, se, ne, s, e ⟩).w ⟩
  sol
  | sw, ⟨ se, ⟨ ne, e ⟩, s ⟩ =>
    ⟨ ⟨ (pb.sol ⟨ sw, se, ne, s, e ⟩).n, (pb.sol ⟨ sw, se, ne, s, e ⟩).coh ⟩ ⟩
  toHom {sw sw'} φ₀
  | ⟨ se, ⟨ ne, e ⟩, s ⟩, ⟨ nw', w' ⟩, ⟨ ⟨ (n' : nw' ⟶ ne), coh' ⟩ ⟩ =>
    ⟨ pb.toHom ⟨ sw, se, ne, s, e ⟩ nw'
      ⟨ w' ≫ φ₀, n'
      , calc
          n' ≫ e = w' ≫ φ₀ ≫ s := coh'
          _ = (w' ≫ φ₀) ≫ s := (C.assoc _ _ _).symm ⟩
    , congrArg PullbackSolution.w <| pb.inv₁ _ _ _ ⟩
  inv₁ {sw sw'} φ₀
  | ⟨ se, ⟨ ne, e ⟩, s ⟩, ⟨ nw', w' ⟩, ⟨ ⟨ (n' : nw' ⟶ ne), coh' ⟩ ⟩ =>
    FibrationalSolution.ext <| Square.ext
    <| congrArg PullbackSolution.n <| pb.inv₁ _ _ _
  inv₂ {sw sw'} φ₀
  | ⟨ se, ⟨ ne, e ⟩, s ⟩, ⟨ nw', w' ⟩, ⟨ (φ : nw' ⟶ _), coh' ⟩ =>
    Square.ext <| calc
        pb.toHom _ _ ⟨ w' ≫ φ₀, φ ≫ (pb.sol _).n, _ ⟩
      = pb.toHom _ _ ⟨ φ ≫ (pb.sol _).w, φ ≫ (pb.sol _).n, _ ⟩
      := congrArg (Pullbacks.toHom _ _) <| PullbackSolution.ext coh'.symm rfl
      _ = φ
      := (pb.inv₂ ⟨ sw, se, ne, s, e ⟩ nw' φ)

end DispBifib
