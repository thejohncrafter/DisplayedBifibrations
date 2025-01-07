
namespace DispBifib

class Hom (α : Sort u) (β : Sort v) (γ : outParam (Sort w)) where
  hom : α → β → γ

infixr:10 " ⟶ " => Hom.hom

class IdxHom
  (α : Sort u) (β : Sort v)
  (base : Sort w)
  (γ : outParam (Sort t))
where
  hom : α → β → base → γ

notation:10 l:11 "[" b:min "]⟶ " r:10 => IdxHom.hom l r b

class Comp (α : Sort u) (β : Sort v) (γ : outParam (Sort w)) where
  comp : α → β → γ

infixr:80 " ≫ " => Comp.comp

class Id (α : Sort u) (φ : outParam (α → α → Sort w)) where
  id : (a : α) → φ a a

notation "𝟙" => Id.id

inductive IdxEq
  {α : Sort u} {F : α → Sort v}
  : {a b : α} → F a → F b → Prop
where
| refl {a : α} (b : F a) : IdxEq b b

infix:50 " =* " => IdxEq

end DispBifib
