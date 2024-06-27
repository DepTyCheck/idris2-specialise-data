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

%default total

ttimps : {0 vs : Vect n Arg} -> AppArgs vs -> Vect n TTImp
ttimps = forget . mapProperty (.ttimp)

||| Tries to symmetrically unify two expressions so that returned substitution being applied to both would give equal expressions
unify : (free : SortedSet Name) -> (ex1, ex2 : TTImp) -> Maybe $ SortedMap Name TTImp

||| Tries to fit `left` expression to be `right` with the returned substitutions
|||
||| Returned substitution can contain only left's free vars as keys.
|||
||| `f a (B x)` being fit with `f (C a d) (B y)` would give `Just $ [`{a} |-> [`(C a d)], `{x} |-> [`(y)]]`
||| `f a a` being fit with `f (C a d) (C a d)` would give `Just $ [`{a} |-> [`(C a d)]]`
||| `f a a` being fit with `f (C a d) (C d a)` would give `Just $ [`{a} |-> [`(C a d), `(C d a)]]`
||| `f a a` being fit with `f (C a d) x` would give `Just $ [`{a} |-> [`(C a d), `{x}]]`
||| `f (D a) (B x)` being fit with `f (C a d) (B y)` would give `Nothing`
||| `f (D a) (B x)` being fit with `f a (B y)` would give `Nothing` too, since `fit` is asymmetrical
-- NOTICE! Current implementation does not try to reorder auto-implicit and named implicit applications.
--         That is, it considers `f a @{b}` and `f @{b} a` to be different things, as well as `f a {n=b}` and `f {n=b} a`, which is not correct.
--         We suppose to work with compiled applications which seems to be normalised somehow.
--         Interesting thing is that if some auto-implicit has name `n` and is the first auto-implicit one, then `f {n=a}` and `f @{a}` are the same semantically.
--         As far as we understand, these stuff are normalised during typechecking too.
--
-- Maybe, better signature would be
-- `fit : (leftFreeVars : Vect n Name) -> (left, right : TIImp) -> Maybe $ Vect n $ List TTImp`
-- This underlines the fact that returned map is a map of free variables to some expressions.
fit : (leftFreeVars : SortedSet Name) -> (left, right : TTImp) -> Maybe $ SortedMap Name $ List1 TTImp
fit leftFreeVars (IVar _ nm                          ) right = if leftFreeVars `contains'` nm then Just $ singleton nm $ singleton right else case right of
                                                                 IVar _ nm' => if nm == nm' then Just empty else Nothing
                                                                 _          => Nothing
fit leftFreeVars (IPi fc rig pinfo mnm argTy retTy   ) right = ?fit_rhs_1
fit leftFreeVars (ILam fc rig pinfo mnm argTy lamTy  ) right = ?fit_rhs_2
fit leftFreeVars (ILet fc lhsFC rig nm nTy nVal scope) right = ?fit_rhs_3
fit leftFreeVars (ICase fc xs s ty cls               ) right = ?fit_rhs_4
fit leftFreeVars (ILocal fc decls s                  ) right = ?fit_rhs_5
fit leftFreeVars (IUpdate fc upds s                  ) right = ?fit_rhs_6
fit leftFreeVars (IApp fc s t                        ) right = ?fit_rhs_7
fit leftFreeVars (INamedApp fc s nm t                ) right = ?fit_rhs_8
fit leftFreeVars (IAutoApp fc s t                    ) right = ?fit_rhs_9
fit leftFreeVars (IWithApp fc s t                    ) right = ?fit_rhs_10
fit leftFreeVars (ISearch fc depth                   ) right = ?fit_rhs_11
fit leftFreeVars (IAlternative fc x ss               ) right = ?fit_rhs_12
fit leftFreeVars (IRewrite fc s t                    ) right = ?fit_rhs_13
fit leftFreeVars (IBindHere fc bm s                  ) right = ?fit_rhs_14
fit leftFreeVars (IBindVar fc str                    ) right = ?fit_rhs_15
fit leftFreeVars (IAs fc nameFC side nm s            ) right = ?fit_rhs_16
fit leftFreeVars (IMustUnify fc dr s                 ) right = ?fit_rhs_17
fit leftFreeVars (IDelayed fc lr s                   ) right = ?fit_rhs_18
fit leftFreeVars (IDelay fc s                        ) right = ?fit_rhs_19
fit leftFreeVars (IForce fc s                        ) right = ?fit_rhs_20
fit leftFreeVars (IQuote fc s                        ) right = ?fit_rhs_21
fit leftFreeVars (IQuoteName fc nm                   ) right = ?fit_rhs_22
fit leftFreeVars (IQuoteDecl fc decls                ) right = ?fit_rhs_23
fit leftFreeVars (IUnquote fc s                      ) right = ?fit_rhs_24
fit leftFreeVars (IPrimVal fc c                      ) right = ?fit_rhs_25
fit leftFreeVars (IType fc                           ) right = ?fit_rhs_26
fit leftFreeVars (IHole fc str                       ) right = ?fit_rhs_27
fit leftFreeVars (Implicit fc bindIfUnsolved         ) right = ?fit_rhs_28
fit leftFreeVars (IWithUnambigNames fc xs s          ) right = ?fit_rhs_29

allVarNames' : TTImp -> SortedSet Name
allVarNames' = runConst . mapATTImp' f where
  f : TTImp -> Const (SortedSet Name) TTImp -> Const (SortedSet Name) TTImp
  f (IVar _ n) = const $ MkConst $ singleton n
  f _          = id

applySubst : SortedMap Name TTImp -> TTImp -> TTImp
applySubst subst = mapTTImp $ \case
  e@(IVar _ n) => fromMaybe e $ lookup n subst
  e => e

Functor PiInfo where
  map f ImplicitArg     = ImplicitArg
  map f ExplicitArg     = ExplicitArg
  map f AutoImplicit    = AutoImplicit
  map f $ DefImplicit x = DefImplicit $ f x

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

fit' : (leftFreeVars : SortedSet Name) -> (left : TTImp) ->
       (rightFreeVars : SortedSet Name) -> (right : TTImp) ->
       Maybe $ SortedMap Name TTImp

-- todo to return clause for `to` and `from` convertions
specCon : (newTyName, newConName : Name) ->
          (extArgs : List Arg) -> (ty : TypeInfo) -> (con : Con _ ty.args) -> (appArgs : Vect ty.arty TTImp) -> Maybe ITy
specCon newTyName newConName extArgs ty con appArgs = do
  let freeCon = fromList $ mapMaybe name $ toList con.args
  let freeExt = fromList $ mapMaybe name extArgs

  let conTy = appAll ty.name $ toList $ ttimps con.typeArgs
  let extTy = appAll ty.name $ toList appArgs

  subst <- fit' freeCon conTy freeExt extTy

  -- TODO to ensure names in substitution RHS (`namesInSubst`) do not overlap free names of the constructor (`freeCon`)

  let namesInSubst = concatMap allVarNames' $ Prelude.toList subst
  let newFreeExtArgs = flip filter extArgs $ maybe False (contains' namesInSubst) . name

  let namesToBeReplaced = keySet subst
  let oldArgsToBeLeft = flip filter (toList con.args) $ maybe True (not . contains' namesToBeReplaced) . name
  let oldArgsToBeLeft = oldArgsToBeLeft <&> {type $= applySubst subst, piInfo $= map $ applySubst subst}

  let newArgs = newFreeExtArgs ++ oldArgsToBeLeft
  pure $ mkTy newTyName $ piAll newTyName.nameVar newArgs

specType : MonadError (FC, String) m => (extArgs : List Arg) -> (ty : TypeInfo) -> (appArgs : Vect ty.arty TTImp) -> m SpecData

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
--sotrue = %ruNElab specialisation $ So True

sofalse : SpecData
--sofalse = %ruNElab specialisation $ So False

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
