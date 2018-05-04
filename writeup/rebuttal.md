First of all, we would like to thank all the reviewers for the detailed comments, which will definitely improve the paper.

Both reviewer #B and reviewer #C suggest moving the `Rose` example before the "Design Space" section. Our goal with the "Design Space" section was to situate our work clearly among the many competing approaches to generic programming as soon as possible, so we could speak about our novelties. But indeed, the core problem --- that of representing mutually recursive families in a sum-of-products fashion --- can be introduced much earlier, and would make the potential reader more interested in the subject.

Reviewer #B mentions that a closed representation of atoms has more disadvantages than benefits. Although for our particular use cases a closed universe is better, there is in fact a trade-off, and our wording should be less intense. In addition, it is possible to provide *both* approaches in the same package, if one takes the following as the type of constants and singletons:

```haskell
type Star = (*)

data Value (t :: Star) :: * where
  Value :: t -> Value t
```

In order to compile that code, however, one has to turn on the TypeInType extension in GHC.

We also make heavy use of the closed universe to decide which types to include in a family of types in our Template Haskell part. Without a choice of "opaque types", a datatype could unravel to include half of the base library. On the other hand, this choice might be given in another form than via a datatype, maybe as an additional argument to the Template Haskell function.

Reviewer #A asks whether in `[[Int]]` we could distinguish between outler and inner lists. The answer is affirmative: in fact the representation in our library would consist of two codes, one corresponding to `[[Int]]` and one to `[Int]`.

Reviewer #A asks why the choice of using a relation between types and codes instead of a function, as done in most other generic programming libraries. We agree that in the `Family` presented in page 13 there is not much again, apart from not writing `Codes f` repeatedly. However, for the version in page 16, where the set of "opaque types" may change, we really have a relation. A single family is represented by different codes depending on that choice.

Reviewer #C asks about the limitations of the approach. As we mention in Section 7, we can only handle a subset of types of kind `*`; we cannot work with GADTs. Also it is important to have a bounded number of types taking place in the family. For example, if one tries to encode:

```haskell
data X a = End | OneMore a (X [a])
```

we would need to generate codes for `X Int`, `X [Int]`, `X [[Int]]`, and so on.

If the user tries to go beyond what is allowed, two different things may happen depending on the stage in compilation. If the programmer uses Template Haskell, he/she is notified whenever a non-supported type is found. If the `Family` declaration is written by hand, the well-typedness of `from` and `to` ensures that everything is in order.