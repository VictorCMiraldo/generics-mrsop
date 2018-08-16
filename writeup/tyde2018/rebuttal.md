First of all, we would like to thank all the reviewers for the detailed comments, which will definitely improve the paper.

We agree with reviewers #B and #C that the paper would benefit of reshuffling some sections, and introduce the core problem --- that of representing mutually recursive families in a sum-of-products fashion --- right away, with some compelling example such as rose trees. We are also happy to include a more thorough comparison with `multirec`, as pointed by reviewer #A.

Reviewer #B mentions that a closed representation of atoms has more disadvantages than benefits. Although for our particular use cases a closed universe is better, there is in fact a trade-off, and our wording should be less intense. In addition, it is possible to provide *both* approaches in the same package, if one takes the following as the type of constants and singletons (which requires TypeInType to compile):

```haskell
type Star = (*)

data Value (t :: Star) :: * where
  Value :: t -> Value t
```

The main drawback of an open universe is that generic operations need to carry constraints around, leading to types like `(All2 Eq (Code a)) => a -> a -> Bool` as found in the `generics-sop` package. Furthermore, our library includes a map-like operation for the opaque types in a representation.

Reviewer #A asks whether in `[[Int]]` we could distinguish between outter and inner lists. The answer is affirmative: in fact the representation in our library would consist of two codes, one corresponding to `[[Int]]` and one to `[Int]`.

Reviewer #A asks why the choice of using a relation between types and codes instead of a function, as done in most other generic programming libraries. If we look at the version of `Family` in page 16, where the set of "opaque types" may change, we really have a relation: a single family is represented by different codes depending on that set. We have decided to present `Family` in page 13 in the same fashion for the sake of uniformity, but we are happy to change it to an associated type family.

Reviewer #C asks about the limitations of the approach. As we mention in Section 7, we can only handle a subset of types of kind `*`: we cannot work with GADTs not handle all sorts of non-regular recursion. For example, if one tries to encode the following non-regular datatype:

```haskell
data X a = End | OneMore a (X [a])
```

we need codes for `X Int`, `X [Int]`, `X [[Int]]`, and so on. We are happy to expand on this limitation in the paper.

If the user tries to go beyond what is allowed, two different things may happen depending on the stage in compilation. If the programmer uses Template Haskell, he/she is notified whenever a non-supported type is found. If the `Family` declaration is written by hand, the well-typedness of `from` and `to` ensures that everything is in order.