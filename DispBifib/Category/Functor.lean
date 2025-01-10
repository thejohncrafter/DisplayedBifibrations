import DispBifib.Notation

import DispBifib.Category.Category

namespace DispBifib

structure Functor
  (C : Category.{u₁,v₁}) (D : Category.{u₂,v₂})
  : Type (max u₁ u₂ v₁ v₂)
where
  map : C → D
  fmap : {a b : C} → (a ⟶ b) → (map a ⟶ map b)
  fmap_id : ∀ a : C, fmap (𝟙 a) = 𝟙 (map a)
  fmap_comp :
    ∀ {a b c : C},
    ∀ (f : a ⟶ b) (g : b ⟶ c),
      fmap (f ≫ g) = fmap f ≫ fmap g

instance
  (C : Category.{u₁,v₁}) (D : Category.{u₂,v₂})
  : CoeFun (Functor C D) (fun _ => C → D)
where
  coe F := F.map

@[ext]
structure NatTrans
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  (F G : Functor C D)
where
  app : (a : C) → (F a ⟶ G a)
  naturality :
    ∀ {a b : C} (f : a ⟶ b),
      F.fmap f ≫ app b = app a ≫ G.fmap f

def NatTrans.id
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  (F : Functor C D) : NatTrans F F
where
  app a := 𝟙 (F a)
  naturality f := by
    dsimp
    conv => lhs; rw [D.comp_id]
    conv => rhs; rw [D.id_comp]

def NatTrans.comp
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  {F G H : Functor C D}
  (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H
where
  app a := α.app a ≫ β.app a
  naturality _ := by
    dsimp
    conv =>
      lhs; rw [← D.assoc]
      lhs; rw [α.naturality]
    conv =>
      rhs; rw [D.assoc]
      rhs; rw [← β.naturality]
    apply D.assoc

theorem NatTrans.id_comp
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  {F G : Functor C D}
  (α : NatTrans F G) : comp (id F) α = α
:= by
  ext a
  exact D.id_comp _

theorem NatTrans.comp_id
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  {F G : Functor C D}
  (α : NatTrans F G) : comp α (id G) = α
:= by
  ext a
  exact D.comp_id _

theorem NatTrans.assoc
  {C : Category.{u₁,v₁}} {D : Category.{u₂,v₂}}
  {F G H K: Functor C D}
  (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K)
  : comp (comp α β) γ = comp α (comp β γ)
:= by
  ext a
  exact D.assoc _ _ _

def FunctorCategory
  (C : Category.{u₁,v₁}) (D : Category.{u₂,v₂})
  : Category.{max u₁ v₁ u₂ v₂, max u₁ v₂}
where
  obj := Functor C D
  hom F G := NatTrans F G
  id := NatTrans.id
  comp := NatTrans.comp
  id_comp := NatTrans.id_comp
  comp_id := NatTrans.comp_id
  assoc := NatTrans.assoc

infixr:26 " ⇒ " => FunctorCategory

instance
  (C : Category.{u₁,v₁}) (D : Category.{u₂,v₂})
  : CoeFun (C ⇒ D) (fun _ => C → D)
:= inferInstanceAs (CoeFun (Functor C D) (fun _ => C → D))

def Functor.id (C : Category.{u,v}) : C ⇒ C where
  map a := a
  fmap f := f
  fmap_id _ := rfl
  fmap_comp _ _ := rfl

def Functor.comp
  {B : Category.{u₁,v₁}} {C : Category.{u₂,v₂}} {D : Category.{u₃,v₃}}
  (F : B ⇒ C) (G : C ⇒ D)
  : B ⇒ D
where
  map a := G (F a)
  fmap f := G.fmap (F.fmap f)
  fmap_id a := by
    dsimp
    rw [F.fmap_id, G.fmap_id]
  fmap_comp f g := by
    dsimp
    rw [F.fmap_comp, G.fmap_comp]

instance : Id Category.{u,v} (fun C D => C ⇒ D) where
  id := Functor.id

instance
  {B : Category.{u₁,v₁}} {C : Category.{u₂,v₂}} {D : Category.{u₃,v₃}}
  : Comp (B ⇒ C) (C ⇒ D) (B ⇒ D)
where
  comp := Functor.comp

end DispBifib
