# DispBifib

I want to study bifibrations in their displayed formulation.

Goals:
- [ ] Reimplement Displayed Categories [[1]](#1) in Lean
- [ ] Define bifibrations in this setting
- [ ] Study the [Grothendieck construction][grot-cons]
- [ ] Maybe study [monadic descent][monadic-descent]

Auxiliary goals:
- [ ] "Bidisplayed Categories" and their correspondance with spans and
  profunctors

## Commentaries

### Indexed Equality

I introduced _indexed equality_ (should I say displayed equality?), noted `=*`.
It is basically an equality over another equality:
```lean
IdxEq {α : Sort u} {F : α → Sort v} : {a b : α} → F a → F b → Prop
```

It would be useful to create indexed variants of `ext` and `rw`, but that's a
story for another time.

### Functors

I chose to define directly the _category of functors_. Therefore, the notation
`⇒` (`\=>`) maps to `FunctorCategory`, not directly to `Functor`. The rationale
is that categores generalize sets, and that functors generalize funtions.
Therefore, I want my category-theoretic syntax to behave like the usual
set-theoretic (type-theoretic) syntax.

With this approach, the following is valid:
```lean
variable (A B C : Category)
#check A ⇒ B ⇒ C
```

## References

<a name="1">[1]</a> Ahrens, B., & Lumsdaine, P. L. (2019). Displayed categories. _Logical Methods in Computer Science_, _15_.
<https://doi.org/10.23638/LMCS-15(1:20)2019>
[arXiv.org:1705.04296](https://arxiv.org/abs/1705.04296)



[monadic-descent]: https://ncatlab.org/nlab/show/monadic+descent
[grot-cons]: https://ncatlab.org/nlab/show/Grothendieck+construction