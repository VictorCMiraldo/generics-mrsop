# Revision history for generics-mrsop

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

* First version. Released on an unsuspecting world.
