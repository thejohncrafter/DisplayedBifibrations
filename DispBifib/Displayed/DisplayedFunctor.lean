import DispBifib.Notation
import DispBifib.IdxEq
import DispBifib.Category

import DispBifib.Displayed.DisplayedCategory

namespace DispBifib

protected structure Functor.Displayed
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  (C : Category.Displayed C₀) (D : Category.Displayed D₀)
  (F : C₀ ⇒ D₀)
where
  map : {a₀ : C₀} → (a : C a₀) → D (F a₀)
  fmap
    : {a₀ b₀ : C₀} → {a : C a₀} → {b : C b₀}
    → {f₀ : a₀ ⟶ b₀} → (a [f₀]⟶ b) → ((map a) [ F.fmap f₀ ]⟶ map b)
  fmap_id : ∀ {a₀ : C₀} (a : C a₀), fmap (𝟙 a) =* 𝟙 (map a)
  fmap_comp :
    ∀ {a₀ b₀ c₀ : C₀} {a : C a₀} {b : C b₀} {c : C c₀},
    ∀ {f₀ : a₀ ⟶ b₀} {g₀ : b₀ ⟶ c₀} (f : a [f₀]⟶ b) (g : b [g₀]⟶ c),
      fmap (f ≫ g) =* fmap f ≫ fmap g

instance
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  (C : Category.Displayed C₀) (D : Category.Displayed D₀)
  (F : C₀ ⇒ D₀)
  : CoeFun (Functor.Displayed C D F) (fun _ => {a : C₀} → C a → D (F a))
where
  coe F := F.map

@[ext]
protected structure NatTrans.Displayed
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ : Functor C₀ D₀}
  (F : Functor.Displayed C D F₀) (G : Functor.Displayed C D G₀)
  (α : NatTrans F₀ G₀)
where
  app : {a₀ : C₀} → (a : C a₀) → ((F a) [α.app a₀]⟶ G a)
  naturality :
    ∀ {a₀ b₀: C₀} {a : C a₀} {b : C b₀} {f₀ : a₀ ⟶ b₀} (f : a [f₀]⟶ b),
      F.fmap f ≫ app b =* app a ≫ G.fmap f

theorem NatTrans.Displayed.ext'
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ : Functor C₀ D₀}
  {F : Functor.Displayed C D F₀} {G : Functor.Displayed C D G₀}
  {α₀ β₀ : NatTrans F₀ G₀}
  {α : NatTrans.Displayed F G α₀} {β : NatTrans.Displayed F G β₀}
  (base : α₀ = β₀)
  (app : ∀ {a₀ : C₀} (a : C a₀), α.app a =* β.app a)
  : α =* β
:= by
  subst base
  apply idx_eq_of_eq
  ext a₀ a
  apply eq_of_idx_eq
  exact app a

def NatTrans.Displayed.id
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ : C₀ ⇒ D₀} (F : Functor.Displayed C D F₀) : NatTrans.Displayed F F (id F₀)
where
  app a := 𝟙 (F a)
  naturality f := by
    dsimp
    have p := D.comp_id (F.fmap f)
    have q := IdxEq.symm <| D.id_comp (F.fmap f)
    exact IdxEq.trans p q

def NatTrans.Displayed.comp
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ H₀ : C₀ ⇒ D₀}
  {F : Functor.Displayed C D F₀}
  {G : Functor.Displayed C D G₀}
  {H : Functor.Displayed C D H₀}
  {α₀ : NatTrans F₀ G₀} {β₀ : NatTrans G₀ H₀}
  (α : NatTrans.Displayed F G α₀) (β : NatTrans.Displayed G H β₀)
  : NatTrans.Displayed F H (comp α₀ β₀)
where
  app a := α.app a ≫ β.app a
  naturality {_ _ a b _} f := by
    have p₁ := D.assoc (F.fmap f) (α.app _) (β.app _)
    have p₂ := α.naturality f
    have p₃ := idxCongrArg (· ≫ β.app b) p₂
    have p := IdxEq.trans p₁.symm p₃
    have q₁ := D.assoc (α.app _) (β.app _) (H.fmap f)
    have q₂ := β.naturality f
    have q₃ := idxCongrArg (α.app a ≫ ·) q₂
    have q := IdxEq.trans q₃ q₁.symm
    exact IdxEq.trans3 p (D.assoc _ _ _) q

theorem NatTrans.Displayed.id_comp
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ : Functor C₀ D₀}
  {F : Functor.Displayed C D F₀}
  {G : Functor.Displayed C D G₀}
  {α₀ : NatTrans F₀ G₀} (α : NatTrans.Displayed F G α₀)
  : comp (id F) α =* α
:= by
  apply NatTrans.Displayed.ext'
  . apply NatTrans.id_comp
  . intro _ _
    exact D.id_comp _

theorem NatTrans.Displayed.comp_id
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ : Functor C₀ D₀}
  {F : Functor.Displayed C D F₀}
  {G : Functor.Displayed C D G₀}
  {α₀ : NatTrans F₀ G₀} (α : NatTrans.Displayed F G α₀)
  : comp α (id G) =* α
:= by
  apply NatTrans.Displayed.ext'
  . apply NatTrans.comp_id
  . intro _ _
    exact D.comp_id _

theorem NatTrans.Displayed.assoc
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  {C : Category.Displayed C₀} {D : Category.Displayed D₀}
  {F₀ G₀ H₀ K₀ : C₀ ⇒ D₀}
  {F : Functor.Displayed C D F₀}
  {G : Functor.Displayed C D G₀}
  {H : Functor.Displayed C D H₀}
  {K : Functor.Displayed C D K₀}
  {α₀ : NatTrans F₀ G₀} {β₀ : NatTrans G₀ H₀} {γ₀ : NatTrans H₀ K₀}
  (α : NatTrans.Displayed F G α₀)
  (β : NatTrans.Displayed G H β₀)
  (γ : NatTrans.Displayed H K γ₀)
  : comp (comp α β) γ =* comp α (comp β γ)
:= by
  apply NatTrans.Displayed.ext'
  . apply NatTrans.assoc
  . intro _ _
    exact D.assoc _ _ _

def FunctorCategory.Displayed
  {C₀ : Category.{u₁,v₁}} {D₀ : Category.{u₂,v₂}}
  (C : Category.Displayed C₀) (D : Category.Displayed D₀)
  : Category.Displayed (C₀ ⇒ D₀)
where
  obj := Functor.Displayed C D
  hom := NatTrans.Displayed
  id := NatTrans.Displayed.id
  comp := NatTrans.Displayed.comp
  id_comp := NatTrans.Displayed.id_comp
  comp_id := NatTrans.Displayed.comp_id
  assoc := NatTrans.Displayed.assoc

end DispBifib
