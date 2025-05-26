
import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category.Category
import DispBifib.Category.Functor

namespace DispBifib

structure PullbackProblem (C : Category u v) where
  sw : C
  se : C
  ne : C
  s : sw ⟶ se
  e : ne ⟶ se

@[ext]
structure PullbackSolution {C : Category u v}
  (pb : PullbackProblem C) (nw : C)
where
  w : nw ⟶ pb.sw
  n : nw ⟶ pb.ne
  coh : n ≫ pb.e = w ≫ pb.s

def PullbackSolution.pullback {C : Category u v}
  {pb : PullbackProblem C}
  {x y : C} (φ : y ⟶ x) (data : PullbackSolution pb x)
  : PullbackSolution pb y
where
  w := φ ≫ data.w
  n := φ ≫ data.n
  coh := calc
    _ = (φ ≫ data.n) ≫ pb.e := rfl
    _ = φ ≫ data.n ≫ pb.e := C.assoc _ _ _
    _ = φ ≫ data.w ≫ pb.s := congrArg (φ ≫ ·) data.coh
    _ = (φ ≫ data.w) ≫ pb.s := Eq.symm <| C.assoc _ _ _

class Pullbacks (C : Category u v) where
  obj : PullbackProblem C → C
  sol : (pb : PullbackProblem C) → PullbackSolution pb (obj pb)
  toHom
    : (pb : PullbackProblem C)
    → (x : C) → PullbackSolution pb x
    → (x ⟶ obj pb)
  inv₁
    : (pb : PullbackProblem C)
    → (x : C) → (s : PullbackSolution pb x)
    → (sol pb).pullback (toHom pb x s) = s
  inv₂
    : (pb : PullbackProblem C)
    → (x : C) → (f : x ⟶ obj pb)
    → toHom pb x ((sol pb).pullback f) = f

def pullback
  {C : Category u v} [Pullbacks C]
  {sw se ne : C} (s : sw ⟶ se) (e : ne ⟶ se)
  : C
:= Pullbacks.obj ⟨ sw, se, ne, s, e ⟩

def pullback_w
  {C : Category u v} [Pullbacks C]
  {sw se ne : C} (s : sw ⟶ se) (e : ne ⟶ se)
  : pullback s e ⟶ sw
:= (Pullbacks.sol ⟨ sw, se, ne, s, e ⟩).w

def pullback_n
  {C : Category u v} [Pullbacks C]
  {sw se ne : C} (s : sw ⟶ se) (e : ne ⟶ se)
  : pullback s e ⟶ ne
:= (Pullbacks.sol ⟨ sw, se, ne, s, e ⟩).n

def pullback_coh
  {C : Category u v} [Pullbacks C]
  {sw se ne : C} (s : sw ⟶ se) (e : ne ⟶ se)
  : pullback_n s e ≫ e = pullback_w s e ≫ s
:= (Pullbacks.sol ⟨ sw, se, ne, s, e ⟩).coh

end DispBifib
