import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

namespace DispBifib

universe u v

protected structure Quiver.Displayed
  (Q₀ : Quiver.{u,v})
  : Type (max u v + 1)
where
  obj : Q₀.obj → Type u
  hom : {a b : Q₀.obj} → obj a → obj b → (a ⟶ b) → Type v

instance
  (Q₀ : Quiver.{u,v})
  : CoeFun (Quiver.Displayed Q₀) (fun _ => Q₀ → Type u)
where
  coe Q := Q.obj

instance
  {Q₀ : Quiver.{u,v}} (Q : Quiver.Displayed Q₀)
  {a₀ b₀ : Q₀} : IdxHom (Q a₀) (Q b₀) (a₀ ⟶ b₀) (Type v)
where
  hom := Q.hom

protected structure Magma.Displayed (M₀ : Magma.{u,v})
  extends Quiver.Displayed M₀.toQuiver
where
  id : {a₀ : M₀} → (a : obj a₀) → (a [𝟙 a₀]⟶ a)
  comp
    : {a₀ b₀ c₀ : M₀}
    → {a : obj a₀} → {b : obj b₀} → {c : obj c₀}
    → {f : a₀ ⟶ b₀} → {g : b₀ ⟶ c₀}
    → (a [f]⟶ b) → (b [g]⟶ c) → (a [f ≫ g]⟶ c)

instance
  (M₀ : Magma.{u,v})
  : CoeFun (Magma.Displayed M₀) (fun _ => M₀ → Type u)
where
  coe M := M.obj

instance
  {M₀ : Magma.{u,v}} (M : Magma.Displayed M₀)
  {a₀ : M₀} : Id (M a₀) (fun a b => a [ 𝟙 a₀ ]⟶ b)
where
  id := M.id

instance
  {M₀ : Magma.{u,v}} (M : Magma.Displayed M₀)
  {a₀ b₀ c₀ : M₀} (a : M a₀) (b : M b₀) (c : M c₀)
  (f : a₀ ⟶ b₀) (g : b₀ ⟶ c₀)
  : Comp (a [f]⟶ b) (b [g]⟶ c) (a [f ≫ g]⟶ c)
where
  comp := M.comp

protected structure Category.Displayed (C₀ : Category.{u,v})
  extends Magma.Displayed C₀.toMagma
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

instance
  (C₀ : Category.{u,v})
  : CoeFun (Category.Displayed C₀) (fun _ => C₀ → Type u)
where
  coe C := C.obj

end DispBifib
