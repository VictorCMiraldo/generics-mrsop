# Revision history for generics-mrsop

## 2.2.0 -- Sep 2019

- Brought in `NS` and `NP` from `sop-core` instead of defining it ourselfes.
  The most striking change is that our old `NP0` is now called `Nil`
- Added pattern synonyms for `NS.Z` and `NS.S`, namelly, `Here` and `There`
- Declared pattern synonyms as `{-# COMPLETE ... #-}`
- Removed `EqHO` and `ShowHO` in favor of quantified constraints `forall x . Eq (f x)`
- Removed `Generics.MRSOP.Zipper.Deep`: No use up to this point and the new
  quantified constraints would require some intervention.
- started using hpack
- The `deriveFamily` now supports reviving families with type synonyms; Pattern
synonyms for `Tag`s will only be generate for the types directly in use at the family.


## 2.1.0 -- Jul 2019

- Added datatype `Holes` for representing families annotated with holes.
- Brought in some monadic attribute grammar combinators
- Big documentation update on a number of places

## 2.0.0 -- Mar 2019

- `Eq1` and `Show1` are now called `EqHO` and `ShowHO`. This avoids clashing with the
already existing `Eq1` in `Prelude`. 
- A number of functions received a `IsNat` constraint.
- `Generics.MRSOP.Util` is now re-exported by `Generics.MRSOP.Base`.
- Support for inheritted attributes no longer exists in `Generics.MRSOP.AG`
- `Fix` is no longer implemented by `AnnFix`. The later now lives in `Generics.MRSOP.AG`

## 1.2.2 -- Sep 2018

- added monadic catamorphism for NP
- added pattern signature generation for TH
- require `TestEqualiy` for opaque types singleton
- Zippers over deep representations
- Refined `Metadata` handling
- `Fix` is implemented as `AnnFix`

## 1.0.0.0  -- May 2018

- First version. Released on an unsuspecting world.
