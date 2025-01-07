import DispBifib.Notation

namespace DispBifib

universe u v

structure Quiver where
  obj : Sort u
  hom : obj → obj → Sort v

instance : CoeSort Quiver.{u,v} (Sort u) where
  coe Q := Q.obj

instance (Q : Quiver.{u,v}) : Hom Q Q (Sort v) where
  hom := Q.hom

structure Magma extends Quiver where
  id : (a : obj) → (a ⟶ a)
  comp
    : {a b c : obj}
    → (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

instance : CoeSort Magma.{u,v} (Sort u) where
  coe M := M.obj

@[default_instance]
instance (M : Magma.{u,v}) : Id M (fun a => a ⟶ a) where
  id := M.id

instance (M : Magma.{u,v}) (a b c : M) : Comp (a ⟶ b) (b ⟶ c) (a ⟶ c) where
  comp := M.comp

structure Category extends Magma.{u,v} where
  id_comp : ∀ {a b : obj} (f : a ⟶ b), f ≫ 𝟙 b = f
  comp_id : ∀ {a b : obj} (f : a ⟶ b), 𝟙 a ≫ f = f
  assoc :
    ∀ {a b c d : obj},
    ∀ (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (f ≫ g) ≫ h = f ≫ g ≫ h

instance : CoeSort Category.{u,v} (Sort u) where
  coe C := C.obj

end DispBifib
