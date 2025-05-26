import DispBifib.Notation

namespace DispBifib

universe u v

structure Quiver : Type (max u v + 1) where
  obj : Type u
  hom : obj → obj → Type v

syntax "Quiver " level level : term

macro_rules
| `(Quiver $u:level $v:level) => `(«Quiver».{$u,$v})

instance : CoeSort (Quiver u v) (Type u) where
  coe Q := Q.obj

instance (Q : Quiver u v) : Hom Q Q (Type v) where
  hom := Q.hom

structure Magma extends Quiver u v where
  id : (a : obj) → (a ⟶ a)
  comp
    : {a b c : obj}
    → (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

syntax "Magma " level level : term

macro_rules
| `(Magma $u:level $v:level) => `(«Magma».{$u,$v})

instance : CoeSort (Magma u v) (Type u) where
  coe M := M.obj

instance (M : Magma u v) : Id M (fun a b => a ⟶ b) where
  id := M.id

instance (M : Magma u v) (a b c : M) : Comp (a ⟶ b) (b ⟶ c) (a ⟶ c) where
  comp := M.comp

structure Category extends Magma u v where
  id_comp : ∀ {a b : obj} (f : a ⟶ b), 𝟙 a ≫ f = f
  comp_id : ∀ {a b : obj} (f : a ⟶ b), f ≫ 𝟙 b = f
  assoc :
    ∀ {a b c d : obj},
    ∀ (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      (f ≫ g) ≫ h = f ≫ g ≫ h

syntax "Category " level level : term

macro_rules
| `(Category $u:level $v:level) => `(«Category».{$u,$v})

instance : CoeSort (Category u v) (Type u) where
  coe C := C.obj

end DispBifib
