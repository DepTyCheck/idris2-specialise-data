module Deriving.Specialise.Data

import Control.Applicative.Const

import Control.Monad.Error.Interface

-- to be removed
import Data.Fin

import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Data.Vect.Quantifiers -- workaround of elab script runner's bug #2439

import public Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Types
import Language.Reflection.Utils

import Syntax.IHateParens.Function

%default total

---------------------------
--- Data specialisation ---
---------------------------

public export
record FunDecl where
  constructor MkFunDecl
  funName : Name
  funSig  : TTImp
  funBody : List Clause

public export
record SpecData where
  constructor MkSpecData
  specName  : Name
  specArgs  : List Arg
  specOpts  : List DataOpt
  specCons  : List ITy
  toSpec    : FunDecl
  fromSpec  : FunDecl

record SpecCon where
  constructor MkSpecCon
  conTy   : ITy
  conTo   : Clause
  conFrom : Clause

specCon : (newTyName, newConName, convToName, convFromName : Name) ->
          (extArgs : List Arg) -> (ty : TypeInfo) -> (con : Con _ ty.args) -> (appArgs : Vect ty.arty TTImp) -> Maybe SpecCon
specCon newTyName newConName convToName convFromName extArgs ty con appArgs = do
  let freeCon = fromList $ mapMaybe name $ toList con.args
  let freeExt = fromList $ mapMaybe name extArgs

  let conTy = appAll ty.name $ toList $ ttimps con.typeArgs
  let extTy = appAll ty.name $ toList appArgs

  subst <- fit' freeCon conTy freeExt extTy

  -- TODO to ensure names in substitution RHS (`namesInSubst`) do not overlap free names of the constructor (`freeCon`)

  -- TODO to ensure that recursive calls to the type being specialised are appropriately substituted

  let namesInSubst = concatMap allVarNames' $ Prelude.toList subst
  let newFreeExtArgs = flip filter extArgs $ maybe False (contains' namesInSubst) . name

  let namesToBeReplaced = keySet subst
  let oldArgsToBeLeft = flip filter (toList con.args) $ maybe True (not . contains' namesToBeReplaced) . name
  let oldArgsToBeLeft = oldArgsToBeLeft <&> {type $= applySubst subst, piInfo $= map $ applySubst subst}

  let newArgs = newFreeExtArgs ++ oldArgsToBeLeft
  pure $ MkSpecCon .| mkTy newConName (piAll newTyName.nameVar newArgs) .| ?conTo_impl .| ?conFrom_impl

specType : MonadError (FC, String) m => (extArgs : List Arg) -> (ty : TypeInfo) -> (appArgs : Vect ty.arty TTImp) -> m SpecData
specType extArgs ty appArgs = do
  let newTyName = ?newTyName
  let newConName : Name -> Name = ?newConName
  let convToName = ?convToName
  let convFromName = ?convFromName

  let specCons = flip mapMaybe ty.cons $ \con => specCon newTyName (newConName con.name) convToName convFromName extArgs ty con appArgs

  let newData = iData ?vis newTyName (piAll type extArgs) ?newTyOpts $ conTy <$> specCons

  ?specType_rhs

export
specialisation : (ty : tyTy) -> Elab SpecData
specialisation ty = do
  ty <- quote ty
  let (extArgs, ty) = unLambda ty
  --for_ tyArgs $ \arg => logMsg "debug" 0 "arg \{show arg.name}, type: \{show arg.type}"
  let Just (MkAppView (_, ty) appArgs _) = appView ty
    | Nothing => failAt (getFC ty) "Not an application to a data type name"
  ty <- getInfo' ty
  ?specialisation_rhs

--- Particular examples ---

%language ElabReflection

listnat : SpecData
--listnat = %runElab specialisation $ List Nat

sotrue : SpecData
--sotrue = %runElab specialisation $ So True

sofalse : SpecData
--sofalse = %runElab specialisation $ So False

listfin : SpecData
--listfin = %runElab specialisation $ \i => List $ Fin i

listfin' : SpecData
--listfin' = %runElab specialisation $ List . Fin

equalbool : SpecData
--equalbool = %runElab specialisation $ Equal {a=Bool} {b=Bool}

equalabool : SpecData
--equalabool = %runElab specialisation $ \a => Equal {a} {b=Bool}

equalnat : SpecData
--equalnat = %runElab specialisation $ Equal Nat Nat

equallistnat : SpecData
--equallistnat = %runElab specialisation $ Equal (List Nat) (List Nat)

equallistnatnat : SpecData
--equallistnatnat = %runElab specialisation $ Equal (List Nat) Nat

listfinfintonat : SpecData
--listfinfintonat = %runElab specialisation $ \i => List $ Fin $ finToNat i

vnat : SpecData
--vnat = %runElab specialisation $ \n => Vect n Nat

vn, vn' : SpecData
-- both should fail as not supported yet (requires closuring mechanism)
--vn = %runElab specialisation $ \a => Vect 5 a
--vn' = %runElab specialisation $ Vect 5 Nat

data X : Type -> Type where
  AnyTy : X a
  AnyList : X (List a)

xlistnat : SpecData
--xlistnat = %runElab specialisation $ X $ List Nat

xnat : SpecData
--xnat = %runElab specialisation $ X Nat
