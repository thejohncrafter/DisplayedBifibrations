import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category
import DispBifib.Displayed

import DispBifib.Examples.Pullbacks

namespace DispBifib

def Typ : Category 1 0 where
  obj := Type
  hom A B := A → B
  id _ a := a
  comp f g x := g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

structure Pullback (A B C : Type) (f : A → B) (g : C → B) where
  a : A
  c : C
  coh : g c = f a

instance : Pullbacks Typ where
  obj | ⟨ sw, se, ne, s, e ⟩ => Pullback sw se ne s e
  sol _ := ⟨ Pullback.a, Pullback.c, funext <| Pullback.coh ⟩
  toHom | _, _, ⟨ w, n, coh ⟩, x => ⟨ w x, n x, congrFun coh x ⟩
  inv₁ _ _ _ := rfl
  inv₂ _ _ _ := rfl

end DispBifib
