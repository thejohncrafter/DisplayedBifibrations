import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

namespace DispBifib

universe u' v' u v

structure DisplayedQuiver
  (Q₀ : Quiver u v)
  : Type (max u v u' v' + 1)
where
  obj : Q₀.obj → Type u'
  hom : {a b : Q₀.obj} → obj a → obj b → (a ⟶ b) → Type v'

syntax "DisplayedQuiver " level level (term:arg)+ : term

macro_rules
| `(DisplayedQuiver $u':level $v':level $args*) => `(«DisplayedQuiver».{$u',$v'} $args*)

instance
  (Q₀ : Quiver u v)
  : CoeFun (DisplayedQuiver u' v' Q₀) (fun _ => Q₀ → Type u')
where
  coe Q := Q.obj

instance
  {Q₀ : Quiver u v} (Q : DisplayedQuiver u' v' Q₀)
  {a₀ b₀ : Q₀} : IdxHom (Q a₀) (Q b₀) (a₀ ⟶ b₀) (Type v')
where
  hom := Q.hom

structure DisplayedMagma (M₀ : Magma u v)
  extends DisplayedQuiver u' v' M₀.toQuiver
where
  id : {a₀ : M₀} → (a : obj a₀) → (a [𝟙 a₀]⟶ a)
  comp
    : {a₀ b₀ c₀ : M₀}
    → {a : obj a₀} → {b : obj b₀} → {c : obj c₀}
    → {f : a₀ ⟶ b₀} → {g : b₀ ⟶ c₀}
    → (a [f]⟶ b) → (b [g]⟶ c) → (a [f ≫ g]⟶ c)

syntax "DisplayedMagma " level level (term:arg)+ : term

macro_rules
| `(DisplayedMagma $u':level $v':level $args*) => `(«DisplayedMagma».{$u',$v'} $args*)

instance
  (M₀ : Magma u v)
  : CoeFun (DisplayedMagma u' v' M₀) (fun _ => M₀ → Type u')
where
  coe M := M.obj

instance
  {M₀ : Magma u v} (M : DisplayedMagma u' v' M₀)
  {a₀ : M₀} : Id (M a₀) (fun a b => a [ 𝟙 a₀ ]⟶ b)
where
  id := M.id

instance
  {M₀ : Magma u v} (M : DisplayedMagma u' v' M₀)
  {a₀ b₀ c₀ : M₀} (a : M a₀) (b : M b₀) (c : M c₀)
  (f : a₀ ⟶ b₀) (g : b₀ ⟶ c₀)
  : Comp (a [f]⟶ b) (b [g]⟶ c) (a [f ≫ g]⟶ c)
where
  comp := M.comp

structure DisplayedCategory (C₀ : Category u v)
  extends DisplayedMagma u' v' C₀.toMagma
where
  id_comp :
    ∀ {a₀ b₀ : C₀} {a : obj a₀} {b : obj b₀},
    ∀ {f₀ : a₀ ⟶ b₀} (f : a [f₀]⟶ b),
      𝟙 a ≫ f =* f
  comp_id :
    ∀ {a₀ b₀ : C₀} {a : obj a₀} {b : obj b₀},
    ∀ {f₀ : a₀ ⟶ b₀} (f : a [f₀]⟶ b),
      f ≫ 𝟙 b =* f
  assoc :
    ∀ {a₀ b₀ c₀ d₀ : C₀} {a : obj a₀} {b : obj b₀} {c : obj c₀} {d : obj d₀},
    ∀ {f₀ : a₀ ⟶ b₀} {g₀ : b₀ ⟶ c₀} {h₀ : c₀ ⟶ d₀},
    ∀ (f : a [f₀]⟶ b) (g : b [g₀]⟶ c) (h : c [h₀]⟶ d),
      (f ≫ g) ≫ h =* f ≫ g ≫ h

syntax "DisplayedCategory " level level (term:arg)+ : term

macro_rules
| `(DisplayedCategory $u':level $v':level $args*) => `(«DisplayedCategory».{$u',$v'} $args*)

instance
  (C₀ : Category u v)
  : CoeFun (DisplayedCategory u' v' C₀) (fun _ => C₀ → Type u')
where
  coe C := C.obj

section Lemmas

theorem idxeq_comp
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  {a₀ b₀ c₀ : C₀} {a : C a₀} {b : C b₀} {c : C c₀}
  {f₀ : a₀ ⟶ b₀} {f : a [ f₀ ]⟶ b}
  {g₀ : a₀ ⟶ b₀} {g : a [ g₀ ]⟶ b}
  (heq : f =* g)
  {h₀ : b₀ ⟶ c₀} (h : b [ h₀ ]⟶ c)
  : f ≫ h =* g ≫ h
:= idxCongrArg (fun {φ₀} (φ : a [ φ₀ ]⟶ b) => φ ≫ h) heq

theorem comp_idxeq
  {C₀ : Category u v} {C : DisplayedCategory u' v' C₀}
  {a₀ b₀ c₀ : C₀} {a : C a₀} {b : C b₀} {c : C c₀}
  {f₀ : a₀ ⟶ b₀} (f : a [ f₀ ]⟶ b)
  {g₀ : b₀ ⟶ c₀} {g : b [ g₀ ]⟶ c}
  {h₀ : b₀ ⟶ c₀} {h : b [ h₀ ]⟶ c}
  (heq : g =* h)
  : f ≫ g =* f ≫ h
:= idxCongrArg (fun {φ₀} (φ : b [ φ₀ ]⟶ c) => f ≫ φ) heq

end Lemmas

end DispBifib
