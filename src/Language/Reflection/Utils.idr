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
toArgument : Arg -> Maybe $ Argument (Count, Maybe Name, TTImp)
toArgument $ MkArg cnt ImplicitArg Nothing ty = Nothing
toArgument $ MkArg cnt ImplicitArg (Just n) ty = Just $ NamedArg EmptyFC n (cnt, Just n, ty)
toArgument $ MkArg cnt ExplicitArg n ty = Just $ Arg EmptyFC (cnt, n, ty)
toArgument $ MkArg cnt AutoImplicit n ty = Just $ AutoArg EmptyFC (cnt, n, ty)
toArgument $ MkArg cnt (DefImplicit x) n ty = Nothing

---------------------------------------------
--- Traversing the `TTImp` data structure ---
---------------------------------------------

public export
interface Unifiable ty where
  fitLeft : (freeInLeft : SortedSet Name) -> (left, right : ty) -> Maybe $ SortedMap Name $ List1 TTImp

private infixl 8 <|+|> -- same as `<+>`

-- compose when both
(<|+|>) : Semigroup a => Maybe a -> Maybe a -> Maybe a
x <|+|> y = [| x <+> y |]

Unifiable a => Unifiable (WithFC a) where
  fitLeft mf (MkFCVal _ x) (MkFCVal _ x') = fitLeft mf x x'

parameters {auto zTTImp : Unifiable TTImp}
  public export
  Unifiable Clause where
    fitLeft mf (PatClause _ lhs rhs) (PatClause _ lhs' rhs') = fitLeft mf lhs lhs' <|+|> fitLeft mf rhs rhs'
    fitLeft mf (WithClause _ l c w pn fs cs) (WithClause _ l' c' w' pn' fs' cs') =
      if c /= c' || fs /= fs' then Nothing else -- todo to manage `pn` and `pn'`
      fitLeft mf l l' <|+|> fitLeft mf w w' <|+|> concatMap (uncurry $ assert_total fitLeft mf) (cs `zip` cs')
    fitLeft mf (ImpossibleClause _ l) (ImpossibleClause _ l') = fitLeft mf l l'
    fitLeft mf _ _ = neutral

  public export
  Unifiable IFieldUpdate where
    fitLeft mf (ISetField p t) (ISetField p' t') = ?foo_104
    fitLeft mf (ISetFieldApp p t) (ISetFieldApp p' t') = ?foo_105
    fitLeft mf _ _ = neutral

  public export
  Unifiable AltType where
    fitLeft mf (FirstSuccess   ) (FirstSuccess    ) = ?foo_107
    fitLeft mf (Unique         ) (Unique          ) = ?foo_108
    fitLeft mf (UniqueDefault t) (UniqueDefault t') = ?foo_109
    fitLeft mf _ _ = neutral

  public export
  Unifiable FnOpt where
    fitLeft mf Inline Inline = ?foo_111
    fitLeft mf NoInline NoInline = ?foo_112
    fitLeft mf Deprecate Deprecate = ?foo_113
    fitLeft mf TCInline TCInline = ?foo_114
    fitLeft mf (Hint b) (Hint b') = ?foo_115
    fitLeft mf (GlobalHint b) (GlobalHint b') = ?foo_116
    fitLeft mf ExternFn ExternFn = ?foo_117
    fitLeft mf (ForeignFn es) (ForeignFn es') = ?foo_118
    fitLeft mf (ForeignExport es) (ForeignExport es') = ?foo_119
    fitLeft mf Invertible Invertible = ?foo_120
    fitLeft mf (Totality tr) (Totality tr') = ?foo_121
    fitLeft mf Macro Macro = ?foo_122
    fitLeft mf (SpecArgs ns) (SpecArgs ns') = ?foo_123
    fitLeft mf _ _ = neutral

  public export
  Unifiable ITy where
    fitLeft mf (MkTy _ n ty) (MkTy _ n' ty') = ?foo_125

  public export
  Unifiable Data where
    fitLeft mf (MkData _ n tc os dc) (MkData _ n' tc' os' dc') = ?foo_126
    fitLeft mf (MkLater _ n tc) (MkLater _ n' tc') = ?foo_127
    fitLeft mf _ _ = neutral

  public export
  Unifiable IField where
    fitLeft mf (MkIField _ c pi n e) (MkIField _ c' pi' n' e') = ?foo_129

  public export
  Unifiable Record where
    fitLeft mf (MkRecord _ n ps opts cn fs) (MkRecord _ n' ps' opts' cn' fs') = ?foo_130

  public export
  Unifiable IClaimData where
    fitLeft mf (MkIClaimData c v fos t) (MkIClaimData c' v' fos' t') = ?foo_131

  public export
  Unifiable Decl where
    fitLeft mf (IClaim cd) (IClaim cd') = fitLeft mf cd cd'
    fitLeft mf (IData _ v t d) (IData _ v' t' d') = ?foo_132
    fitLeft mf (IDef _ n cs) (IDef _ n' cs') = ?foo_133
    fitLeft mf (IParameters _ ps ds) (IParameters _ ps' ds') = ?foo_134
    fitLeft mf (IRecord _ ns v tr r) (IRecord _ ns' v' tr' r') = ?foo_135
    fitLeft mf (INamespace _ ns ds) (INamespace _ ns' ds') = ?foo_136
    fitLeft mf (ITransform _ n f t) (ITransform _ n' f' t') = ?foo_137
    fitLeft mf (IRunElabDecl _ e) (IRunElabDecl _ e') = ?foo_138
    fitLeft mf (ILog p) (ILog p') = ?foo_139
    fitLeft mf (IBuiltin _ t n) (IBuiltin _ t' n') = ?foo_140
    fitLeft mf _ _ = neutral

---------------------------------------------

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
