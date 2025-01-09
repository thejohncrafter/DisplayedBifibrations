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

## Mathematics

## Indexed, Fibered, Displayed

There are three visions of the same phenomenon of "stuff with some other stuff
on top of it":
- "Fibrational point of view": with a base $B$, this is $(X, f)$
  where $f : X \to B$ (plus possibly some extra conditions on $f$).
  Here, fibers over $x \in B$ are given by $f^{-1}(x)$
  (at least, morally so, this is only an account of the geometrical side of the
  story in the case where spaces have well-behaved points).
- "Indexed point of view": with a base $B$, this is a map
  $B \to \textrm{Spaces}$.
  It is more difficult to _formalize_ the meaning of this, but _morally_
  it's pretty clear (especially for computer scientist who are used to seeing
  `F : A → Type` as a family of types).
- "Displayed point of view": this is a novelty that was introduced by
  [Ahrens & Lumsdaine [1]](#1). That's what I want to discuss here.

## Code Commentaries

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