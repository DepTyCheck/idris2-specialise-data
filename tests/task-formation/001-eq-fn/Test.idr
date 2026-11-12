module Test

import Shared

%language ElabReflection

%default total

withFn : TTImp
withFn = `(Builtin.Equal {a = Prelude.Types.Nat} {b = Prelude.Types.Nat -> Prelude.Types.Nat -> Prelude.Types.Nat} 1 Prelude.minus)

withType : TTImp
withType = `(Builtin.Equal {a = Prelude.Types.Nat} {b = Type} 1 Prelude.Types.Nat)


main : IO ()
main = do
  putPretty $ %runElab runSTR withFn
  putPretty $ %runElab runSTR withType
