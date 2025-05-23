import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category
import DispBifib.Displayed

namespace DispBifib

structure OpfibrationalProblem
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀) (c₀ : C₀)
where
  b₀ : C₀
  b : C b₀
  f₀ : b₀ ⟶ c₀

def OpfibrationalProblem.pullback
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {d₀ c₀ : C₀} (φ₀ : c₀ ⟶ d₀)
  (pb : OpfibrationalProblem C c₀) : OpfibrationalProblem C d₀
where
  b₀ := pb.b₀
  b := pb.b
  f₀ := pb.f₀ ≫ φ₀

@[ext]
structure OpfibrationalSolution
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {c₀ : C₀} (pb : OpfibrationalProblem C c₀) (c : C c₀)
where
  f : pb.b [ pb.f₀ ]⟶ c

def OpfibrationalSolution.pullback
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀}
  {c₀ : C₀} {pb : OpfibrationalProblem C c₀}
  {d₀ : C₀} {d : C d₀} {c : C c₀} {φ₀ : c₀ ⟶ d₀} (φ : c [ φ₀ ]⟶ d)
  (sol : OpfibrationalSolution pb c) : OpfibrationalSolution (pb.pullback φ₀) d
where
  f := sol.f ≫ φ

class Opfibration
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀)
where
  obj : (c₀ : C₀) → OpfibrationalProblem C c₀ → C c₀
  sol : (c₀ : C₀) → (pb : OpfibrationalProblem C c₀) → OpfibrationalSolution pb (obj c₀ pb)
  toHom
    : {c₀ d₀ : C₀} → (φ₀ : c₀ ⟶ d₀)
    → (pb : OpfibrationalProblem C c₀)
    → (d : C d₀) → OpfibrationalSolution (pb.pullback φ₀) d
    → ((obj c₀ pb) [ φ₀ ]⟶ d)
  inv₁
    : {c₀ d₀ : C₀} → (φ₀ : c₀ ⟶ d₀)
    → (pb : OpfibrationalProblem C c₀)
    → (d : C d₀) → (s : OpfibrationalSolution (pb.pullback φ₀) d)
    → (sol c₀ pb).pullback (toHom φ₀ pb d s) = s
  inv₂
    : {c₀ d₀ : C₀} → (φ₀ : c₀ ⟶ d₀)
    → (pb : OpfibrationalProblem C c₀)
    → (d : C d₀) → (φ : (obj c₀ pb) [ φ₀ ]⟶ d)
    → toHom φ₀ pb d ((sol c₀ pb).pullback φ) = φ

def oplift_obj
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {a₀ b₀ : C₀} (f₀ : a₀ ⟶ b₀) (a : C a₀) : C b₀
:= fib.obj b₀ ⟨ a₀, a, f₀ ⟩

def oplift_hom
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {a₀ b₀ : C₀} (f₀ : a₀ ⟶ b₀) (a : C a₀) : (a [ f₀ ]⟶ oplift_obj f₀ a)
:= (fib.sol b₀ ⟨ a₀, a, f₀ ⟩).f

def opfactor
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : (oplift_obj f a) [ w₀ ]⟶ c
:= by
  subst h
  exact fib.toHom w₀ ⟨ x, a, f ⟩ c ⟨ g ⟩

def opfactor_prop
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : oplift_hom f a ≫ opfactor f a g w₀ h =* g
:= by
  subst h
  apply idx_eq_of_eq
  exact congrArg OpfibrationalSolution.f <| fib.inv₁ w₀ ⟨ x, a, f ⟩ c ⟨ g ⟩

def opfactor_unique
  {C₀ : Category.{u,v}} {C : Category.Displayed C₀} [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) (a : C x)
  {c₀ : C₀} {c : C c₀} {g₀ : x ⟶ c₀} (g : a [ g₀ ]⟶ c)
  (w₀ : y ⟶ c₀)
  (h : f ≫ w₀ = g₀)
  : ∀ (w' : (oplift_obj f a) [ w₀ ]⟶ c),
    (oplift_hom f a ≫ w' =* g) → opfactor f a g w₀ h = w'
:= by
  subst h
  intro w' h'
  have h' := eq_of_idx_eq _ h'; subst h'
  exact fib.inv₂ w₀ ⟨ x, a, f ⟩ c w'

def pushforward
  {C₀ : Category.{u,v}} (C : Category.Displayed C₀) [fib : Opfibration C]
  {x y : C₀} (f : x ⟶ y) : fiber C x ⇒ fiber C y
where
  map a := oplift_obj f a
  fmap {a a' : C x} (g : a [ 𝟙 x ]⟶ a') :=
    have p : f ≫ 𝟙 y = 𝟙 x ≫ f := by rw [C₀.id_comp, C₀.comp_id]
    opfactor f a (g ≫ oplift_hom f a') (𝟙 y) p
  fmap_id a := by
    apply opfactor_unique f a
    exact .trans (C.comp_id _) (C.id_comp _).symm
  fmap_comp {a₁ a₂ a₃} g g' := by
    apply opfactor_unique f a₁
    apply IdxEq.trans3
      (comp_idxeq _ (fiber_comp_eq _ _))
      _
      (idxeq_comp (fiber_comp_eq _ _).symm _)
    apply IdxEq.trans3 (C.assoc _ _ _).symm _ (C.assoc _ _ _).symm
    apply IdxEq.trans (idxeq_comp (opfactor_prop f a₁ _ _ _) _) _
    apply IdxEq.trans (C.assoc _ _ _)
    apply comp_idxeq _ (opfactor_prop _ _ _ _ _)

end DispBifib
