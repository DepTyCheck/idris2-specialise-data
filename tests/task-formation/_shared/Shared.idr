module Shared

import public Deriving.SpecialiseData
import public Deriving.SpecialiseData.TaskFormation
import public Language.Reflection.Pretty
import public Text.PrettyPrint.Bernardy

%default total

public export
runSTR : Elaboration m => TTImp -> m $ Maybe (TTImp, List Arg, List $ Maybe TTImp)
runSTR e = do
  niit <- getNamesInfoInTypes' e
  exprToSpecTask specDecideArg e
