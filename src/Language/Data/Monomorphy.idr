module Language.Data.Monomorphy

-- to be removed
import Data.Fin

import Data.Vect -- workaround of elab script runner's bug
import Data.Vect.Quantifiers -- workaround of elab script runner's bug

import public Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Types

%default total

public export
record SpeciRes where
  constructor MkSpeciRes
  extArgs  : List Arg
  specData : Name -> Decl
  toSpec   : Name -> (Decl, Decl)
  fromSpec : Name -> (Decl, Decl)

export
specialisation : (ty : tyTy) -> Elab SpeciRes
specialisation ty = do
  ty <- quote ty
  let (extArgs, ty) = unLambda ty
  --for_ tyArgs $ \arg => logMsg "debug" 0 "arg \{show arg.name}, type: \{show arg.type}"
  let Just (MkAppView (_, ty) appArgs _) = appView ty
    | Nothing => failAt (getFC ty) "Not an application to a data type name"
  ty <- getInfo' ty
  ?specialisation_rhs

%language ElabReflection
x : SpeciRes
--x = %runElab specialisation $ \i => List $ Fin $ finToNat i
