import DispBifib.Notation
import DispBifib.Category

namespace DispBifib

universe u v

structure Quiver.Displayed (Q₀ : Quiver.{u,v}) where
  obj : Q₀.obj → Sort u
  hom : {a b : Q₀.obj} → obj a → obj b → Sort v

instance
  (Q₀ : Quiver.{u,v})
  : CoeFun (Quiver.Displayed Q₀) (fun _ => Q₀ → Sort u)
where
  coe Q := Q.obj

instance
  {Q₀ : Quiver.{u,v}} (Q : Quiver.Displayed Q₀)
  {a₀ b₀ : Q₀} : Hom (Q a₀) (Q b₀) (Sort v)
where
  hom := Q.hom

structure Magma.Displayed (M₀ : Magma.{u,v})
  extends Quiver.Displayed M₀.toQuiver
where
  id : {a₀ : M₀} → (a : obj a₀) → (a ⟶ a)
  comp
    : {a₀ b₀ c₀ : M₀}
    → {a : obj a₀} → {b : obj b₀} → {c : obj c₀}
    → (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

instance
  (M₀ : Magma.{u,v})
  : CoeFun (Magma.Displayed M₀) (fun _ => M₀ → Sort u)
where
  coe M := M.obj

instance
  {M₀ : Magma.{u,v}} (M : Magma.Displayed M₀)
  {a₀ : M₀} : Id (M a₀) (fun a b => a ⟶ b)
where
  id := M.id

instance
  {M₀ : Magma.{u,v}} (M : Magma.Displayed M₀)
  {a₀ b₀ c₀ : M₀} (a : M a₀) (b : M b₀) (c : M c₀)
  : Comp (a ⟶ b) (b ⟶ c) (a ⟶ c)
where
  comp := M.comp

structure Category.Displayed (C₀ : Category.{u,v})
  extends Magma.Displayed C₀.toMagma
where
  id_comp :
    ∀ {a₀ b₀ : C₀} {a : obj a₀} {b : obj b₀},
    ∀ (f : a ⟶ b),
      f ≫ 𝟙 b = f
  comp_id :
    ∀ {a₀ b₀ : C₀} {a : obj a₀} {b : obj b₀},
    ∀ (f : a ⟶ b),
      𝟙 a ≫ f = f
  assoc :
    ∀ {a₀ b₀ c₀ d₀ : C₀} {a : obj a₀} {b : obj b₀} {c : obj c₀} {d : obj d₀},
    ∀ (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (f ≫ g) ≫ h = f ≫ g ≫ h

instance
  (C₀ : Category.{u,v})
  : CoeFun (Category.Displayed C₀) (fun _ => C₀ → Sort u)
where
  coe C := C.obj

end DispBifib
