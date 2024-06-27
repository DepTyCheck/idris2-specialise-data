module Language.Reflection.Utils

import Control.Applicative.Const

import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Data.Vect.Quantifiers -- workaround of elab script runner's bug #2439

import public Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Types

%default total

export
ttimps : {0 vs : Vect n Arg} -> AppArgs vs -> Vect n TTImp
ttimps = forget . mapProperty (.ttimp)

||| Tries to symmetrically unify two expressions so that returned substitution being applied to both would give equal expressions
export
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
export
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

public export
fit' : (leftFreeVars : SortedSet Name) -> (left : TTImp) ->
       (rightFreeVars : SortedSet Name) -> (right : TTImp) ->
       Maybe $ SortedMap Name TTImp

export -- taken actually from DepTyCheck
allVarNames' : TTImp -> SortedSet Name
allVarNames' = runConst . mapATTImp' f where
  f : TTImp -> Const (SortedSet Name) TTImp -> Const (SortedSet Name) TTImp
  f (IVar _ n) = const $ MkConst $ singleton n
  f _          = id

export
applySubst : SortedMap Name TTImp -> TTImp -> TTImp
applySubst subst = mapTTImp $ \case
  e@(IVar _ n) => fromMaybe e $ lookup n subst
  e => e

export
Functor PiInfo where
  map f ImplicitArg     = ImplicitArg
  map f ExplicitArg     = ExplicitArg
  map f AutoImplicit    = AutoImplicit
  map f $ DefImplicit x = DefImplicit $ f x
