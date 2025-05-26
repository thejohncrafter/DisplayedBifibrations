import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category
import DispBifib.Displayed

namespace DispBifib

structure FibrationalProblem
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀) (c₀ : C₀)
where
  b₀ : C₀
  b : C b₀
  f₀ : c₀ ⟶ b₀

def FibrationalProblem.pullback
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  {d₀ c₀ : C₀} (φ₀ : d₀ ⟶ c₀)
  (pb : FibrationalProblem C c₀) : FibrationalProblem C d₀
where
  b₀ := pb.b₀
  b := pb.b
  f₀ := φ₀ ≫ pb.f₀

@[ext]
structure FibrationalSolution
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  {c₀ : C₀} (pb : FibrationalProblem C c₀) (c : C c₀)
where
  f : c [ pb.f₀ ]⟶ pb.b

def FibrationalSolution.pullback
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  {c₀ : C₀} {pb : FibrationalProblem C c₀}
  {d₀ : C₀} {d : C d₀} {c : C c₀} {φ₀ : d₀ ⟶ c₀} (φ : d [ φ₀ ]⟶ c)
  (sol : FibrationalSolution pb c) : FibrationalSolution (pb.pullback φ₀) d
where
  f := φ ≫ sol.f

class Fibration
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀)
where
  obj : (c₀ : C₀) → FibrationalProblem C c₀ → C c₀
  sol : (c₀ : C₀) → (pb : FibrationalProblem C c₀) → FibrationalSolution pb (obj c₀ pb)
  toHom
    : {c₀ d₀ : C₀} → (φ₀ : d₀ ⟶ c₀)
    → (pb : FibrationalProblem C c₀)
    → (d : C d₀) → FibrationalSolution (pb.pullback φ₀) d
    → (d [ φ₀ ]⟶ obj c₀ pb)
  inv₁
    : {c₀ d₀ : C₀} → (φ₀ : d₀ ⟶ c₀)
    → (pb : FibrationalProblem C c₀)
    → (d : C d₀) → (s : FibrationalSolution (pb.pullback φ₀) d)
    → (sol c₀ pb).pullback (toHom φ₀ pb d s) = s
  inv₂
    : {c₀ d₀ : C₀} → (φ₀ : d₀ ⟶ c₀)
    → (pb : FibrationalProblem C c₀)
    → (d : C d₀) → (φ : d [ φ₀ ]⟶ obj c₀ pb)
    → toHom φ₀ pb d ((sol c₀ pb).pullback φ) = φ

def lift_obj
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  [fib : Fibration C]
  {b₀ a₀ : C₀} (f₀ : b₀ ⟶ a₀) (a : C a₀) : C b₀
:= fib.obj b₀ ⟨ a₀, a, f₀ ⟩

def lift_hom
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  [fib : Fibration C]
  {b₀ a₀ : C₀} (f₀ : b₀ ⟶ a₀) (a : C a₀) : (lift_obj f₀ a) [ f₀ ]⟶ a
:= (fib.sol b₀ ⟨ a₀, a, f₀ ⟩).f

def factor
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : c [ w₀ ]⟶ lift_obj f b
:= by
  subst h
  exact fib.toHom w₀ ⟨ y, b, f ⟩ c ⟨ g ⟩

def factor_prop
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : factor f b g w₀ h ≫ lift_hom f b =* g
:= by
  subst h
  apply idx_eq_of_eq
  exact congrArg FibrationalSolution.f <| fib.inv₁ w₀ ⟨ y, b, f ⟩ c ⟨ g ⟩

def factor_unique
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀} [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) (b : C y)
  {c₀ : C₀} {c : C c₀} {g₀ : c₀ ⟶ y} (g : c [ g₀ ]⟶ b)
  (w₀ : c₀ ⟶ x)
  (h : w₀ ≫ f = g₀)
  : ∀ (w' : c [ w₀ ]⟶ lift_obj f b),
    (w' ≫ lift_hom f b =* g) → factor f b g w₀ h = w'
:= by
  subst h
  intro w' h'
  have h' := eq_of_idx_eq _ h'; subst h'
  exact fib.inv₂ w₀ ⟨ y, b, f ⟩ c w'

def pullback
  {C₀ : Category u v} (C : DisplayedCategory u' v' C₀) [fib : Fibration C]
  {x y : C₀} (f : x ⟶ y) : fiber C y ⇒ fiber C x
where
  map b := lift_obj f b
  fmap {b b' : C y} (g : b [ 𝟙 y ]⟶ b') :=
    have p : 𝟙 x ≫ f = f ≫ 𝟙 y := by rw [C₀.id_comp, C₀.comp_id]
    factor f b' (lift_hom f b ≫ g) (𝟙 x) p
  fmap_id b := by
    apply factor_unique f b
    exact .trans (C.id_comp _) (C.comp_id _).symm
  fmap_comp {b₁ b₂ b₃} g g' := by
    dsimp
    apply factor_unique f b₃
    apply IdxEq.trans3
      (idxeq_comp (fiber_comp_eq _ _) _)
      _
      (comp_idxeq _ (fiber_comp_eq _ _).symm)
    apply IdxEq.trans3 (C.assoc _ _ _) _ (C.assoc _ _ _)
    apply IdxEq.trans (comp_idxeq _ (factor_prop f b₃ _ _ _)) _
    apply IdxEq.trans (C.assoc _ _ _).symm
    apply idxeq_comp (factor_prop _ _ _ _ _)

end DispBifib
