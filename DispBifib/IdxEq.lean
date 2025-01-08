
namespace DispBifib

inductive IdxEq
  {α : Sort u} {F : α → Sort v}
  : {a b : α} → F a → F b → Prop
where
| refl {a : α} (b : F a) : IdxEq b b

infix:50 " =* " => IdxEq

section

variable {α : Sort u} {F : α → Sort v}

@[symm]
theorem IdxEq.symm
  {a b : α} {c : F a} {d : F b}
  : c =* d → d =* c
| .refl _ => .refl _

theorem IdxEq.trans
  {a b c : α} {d : F a} {e : F b} {f : F c}
  : d =* e → e =* f → d =* f
| .refl _, .refl _ => .refl _

theorem IdxEq.trans3
  {a₁ a₂ a₃ a₄ : α} {b₁ : F a₁} {b₂ : F a₂} {b₃ : F a₃} {b₄ : F a₄}
  : b₁ =* b₂ → b₂ =* b₃ → b₃ =* b₄ → b₁ =* b₄
| .refl _, .refl _, .refl _ => .refl _

theorem idx_eq_of_eq
  {a : α} {c d : F a}
  : c = d → c =* d
| rfl => .refl _

theorem eq_of_idx_eq
  {a : α} {c d : F a}
  : c =* d → c = d
| .refl _ => rfl

theorem idxCongrArg
  {β : Sort u'} {G : β → Sort v'}
  {a b : α} {c : F a} {d : F b}
  {f₀ : α → β}
  (f : {a : α} → F a → G (f₀ a))
  (h : c =* d)
  : f c =* f d
:= match h with
  | .refl _ => .refl _

end

end DispBifib
