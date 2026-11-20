||| Toplevel code generation functions
module Deriving.SpecialiseData.Codegen

import public Data.DPair -- workaround for idris-lang/Idris2#2439
import Data.Fin
import Data.SnocList
import Data.SnocList.Quantifiers
import public Deriving.SpecialiseData.Codegen.Type -- workaround for idris-lang/Idris2#2439
import public Deriving.SpecialiseData.Codegen.Cast -- workaround for idris-lang/Idris2#2439
import public Deriving.SpecialiseData.Codegen.Claims -- workaround for idris-lang/Idris2#2439
import public Deriving.SpecialiseData.Codegen.InterfaceImpls -- workaround for idris-lang/Idris2#2439
import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.Unification
import Deriving.SpecialiseData.Utils.Quantifiers
import Deriving.SpecialiseData.Utils.TypeInfo
import Language.Reflection.Compat
import Language.Reflection.Expr
import Language.Reflection.Expr.VarSubst
import Language.Reflection.Unify

  ------------------------------------
  --- SPECIALISED TYPE DECLARATION ---
  ------------------------------------

(.declNoNS) : TypeInfo -> Decl
(.declNoNS) ti =
  iData Public tyName tySig [] conITys
  where
    tyName = snd $ unNS ti.name
    tySig = piAll type ti.args
    conITys = (.iTy) <$> ti.cons

export
mkSpecTySig : SpecTask -> Decl
mkSpecTySig t = iDataLater Public t.resultName (piAll type t.ttArgs)

export
specClaims :
  MonadLog m => SpecTask -> UniResults -> (mt : TypeInfo) -> (0 mtNamed : AllTyArgsNamed mt) => TypeMeta -> m $ List Decl
specClaims t uniResults specTy specMeta = do
  let specTySig = mkSpecTySig t
  logPoint DetailedDebug "specialiseData.specDecls.specTy.sig" [t] $ show specTySig
  let mToPImplClaim = mkMToPImplClaim t
  logPoint DetailedDebug "specialiseData.specDecls.mToPImpl.sig" [t] $ show mToPImplClaim
  let mToPClaim = mkMToPClaim t
  logPoint DetailedDebug "specialiseData.specDecls.mToP.sig" [t] $ show mToPClaim
  let decEqClaims : List Decl = [ mkDecEqImplClaim t, mkDecEqClaim t ]
  logPoint DetailedDebug "specialiseData.specDecls.decEq.sig" [t] $ show decEqClaims
  let showClaims = mkShowClaims t
  logPoint DetailedDebug "specialiseData.specDecls.show.sig" [t] $ show showClaims
  let eqClaims = mkEqClaims t
  logPoint DetailedDebug "specialiseData.specDecls.eq.sig" [t] $ show eqClaims
  let pToMImplClaim = mkPToMImplClaim t
  logPoint DetailedDebug "specialiseData.specDecls.pToMImpl.sig" [t] $ show pToMImplClaim
  let pToMClaim = mkPToMClaim t
  logPoint DetailedDebug "specialiseData.specDecls.pToM.sig" [t] $ show pToMClaim
  let fromStringClaims = mkFromStringClaims t
  logPoint DetailedDebug "specialiseData.specDecls.fromString.sig" [t] $ show fromStringClaims
  let numClaims = mkNumClaims t
  logPoint DetailedDebug "specialiseData.specDecls.num.sig" [t] $ show numClaims
  let anyUndecided = any isUndecided uniResults
  let sClaims = join [
      [ mToPImplClaim, mToPClaim]
      , decEqClaims
      , showClaims
      , eqClaims
    ]
  let dClaims = join [
      [ pToMImplClaim, pToMClaim]
      , fromStringClaims
      , numClaims
    ]
  let claims : List Decl = sClaims ++ if anyUndecided then [] else dClaims
  logPoint DetailedDebug "specialiseData.specDecls.claims" [t] $ show claims
  pure $ specTySig :: claims

export
specBodies :
  MonadLog m => SpecTask -> UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TypeMeta -> m $ List Decl
specBodies t uniResults specTy specMeta = do
  let specTyDecl = specTy.declNoNS
  logPoint DetailedDebug "specialiseData.specDecls.specTy" [t] $ show specTyDecl
  let mToPImplDecls = mkMToPImplDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.mToPImpl" [t] $ show mToPImplDecls
  let mToPDecls = mkMToPDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.mToP" [t] $ show mToPDecls
  let castInjDecls = mkCastInjDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.castInj" [t] $ show castInjDecls
  let decEqDecls = mkDecEqDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.decEq" [t] $ show decEqDecls
  let showDecls = mkShowDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.show" [t] $ show showDecls
  let eqDecls = mkEqDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.eq" [t] $ show eqDecls
  let pToMImplDecls = mkPToMImplDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.pToMImpl" [t] $ show pToMImplDecls
  let pToMDecls = mkPToMDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.pToM" [t] $ show pToMDecls
  let fromStringDecls = mkFromStringDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.fromString" [t] $ show fromStringDecls
  let numDecls = mkNumDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.num" [t] $ show numDecls
  let anyUndecided = any isUndecided uniResults
  let decidedDecls =
    [ pToMImplDecls
    , pToMDecls
    , fromStringDecls
    , numDecls
    ]
  let onFull : List Decl =
    if anyUndecided
        then []
        else join decidedDecls
  pure $ join
    [ [ specTyDecl ]
    , mToPImplDecls
    , mToPDecls
    , castInjDecls
    , decEqDecls
    , showDecls
    , eqDecls
    , onFull
    ]


||| Generate declarations for given task, unification results, and specialised type
export
specDecls :
  MonadLog m => SpecTask -> UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TypeMeta -> m $ List Decl
specDecls t uniResults specTy specMeta = do
  claims <- specClaims t uniResults specTy specMeta
  bodies <- specBodies t uniResults specTy specMeta
  pure $ singleton $ INamespace EmptyFC (MkNS [ show t.resultName ]) $ claims ++ bodies
