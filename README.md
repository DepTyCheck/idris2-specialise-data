<!-- idris
module README

import Data.Vect
import Deriving.SpecialiseData

%language ElabReflection
-->
# Dependent data type specialiser

This library is used by [DepTyCheck](https://github.com/buzden/deptycheck) and was formerly part of `elab-util-extra`.

## Specialisation

Specialisation is an operation by which a particular case of a generic type
(for instance, `List Nat`, a case of `List`) may be turned into a
*specialised* type that is equivalent to it.

This library provides a number of subtly different specialisation functions with different error handling conventions and input data formats.
The simplest function to use directly is `specialiseDataLam'`. It takes as arguments the name of emitted specialised type and the invocation of the type being specialised.

Consider the following example: we wish to generate a specialised type `ListNat`
equivalent to `List Nat`.

<!-- idris
namespace Dummy {
%hide Prelude.List
-->
```idris
data List : Type -> Type where
  Nil : List a
  (::) : a -> List a -> List a
```
<!-- idris
%unhide Prelude.List
 }
-->

To do this, we can call `specialiseDataLam'` with the `ListNat` name and `List Nat` invocation:

```idris
%runElab specialiseDataLam' `{ListNat} $ List Nat
```

This will produce the following type:
<!-- idris
namespace DummyLN {
%hide README.ListNat.ListNat
-->
```idris
data ListNat : Type where
  Nil : ListNat
  (::) : Nat -> ListNat -> ListNat
```
<!-- idris
%unhide README.ListNat.ListNat
 }
ln : ListNat
ln = [1,2,3]
-->

Besides the type itself, the specialiser will implement a number of auxiliary interfaces:
- `Cast ListNat (List Nat)`
  - A proof of injectivity (`Injective`) for this cast
- `DecEq (List Nat) => DecEq ListNat` instance that relies on the cast injectivity proof to work
- `Show (List Nat) => Show ListNat`
- `Eq (List Nat) => Eq ListNat`
- `Cast (List Nat) ListNat`[^1]
- `FromString (List Nat) => FromString ListNat`[^1]
- `Num (List Nat) => Num ListNat`[^1]

[^1]: If no ambiguous constructors present

It is not required to fully specify all arguments of the type when specialising. For instance, to produce a `Vect` of `Nat` values, the specialiser invocation will look like this:

```idris
%runElab specialiseDataLam' `{VectNat} $ \n => Vect n Nat
```

<!-- idris
vn : VectNat 3
vn = [1,2,3]
-->

When specialising GADTs, the specialised type will consist only of constructors whose return signatures match the given invocation.

### Limitations

- In certain cases, we cannot determine if the constructor return signature matches the given invocation. Such constructors are omitted from the specialised type.
  As a consequence, the specialised type will be *lossy* rather than fully equivalent, and some interfaces won't be implemented.
  This mainly occurs when specifying complex values to a type's non-type arguments, i.e. trying to specialise `\a, b => Vect (a + b) Nat`.

  This is intended as a temporary fallback behaviour, with a proper fix planned in the future.
- Presently the specialiser is single-pass, and will not recursively specialise generic types present in the type's fields. This means that, although the specialiser correctly preserves direct recursion, this is not true for mutually recursive types, which may lead to unexpected behaviour.

