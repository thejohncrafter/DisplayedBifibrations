
namespace DispBifib

class Hom (α : Sort u) (β : Sort v) (γ : outParam (Sort w)) where
  hom : α → β → γ

infixr:10 " ⟶ " => Hom.hom

class Comp (α : Sort u) (β : Sort v) (γ : outParam (Sort w)) where
  comp : α → β → γ

infixr:80 " ≫ " => Comp.comp

class Id (α : Sort u) (φ : outParam (α → α → Sort w)) where
  id : (a : α) → φ a a

notation "𝟙" => Id.id

end DispBifib
