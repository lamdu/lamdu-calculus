{-# LANGUAGE OverloadedStrings, TypeFamilyDependencies #-}

import Control.Lens (at)
import Control.Lens.Operators
import Data.Set (fromList)
import Hyper
import Hyper.Type.AST.Scheme
import Lamdu.Calc.Infer
import Lamdu.Calc.Type
import Test.Framework
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertBool)

alphaEqTest :: Test
alphaEqTest =
    not (alphaEq (f (TVarP "a")) (f (TRecordP REmptyP)))
    & assertBool "should alpha eq"
    & testCase "alpha-eq"
    where
        f x =
            TFunP (TVarP "a") (TVariantP (RExtendP "t" x (RVarP "c"))) ^. hPlain
            & Scheme
                ( Types
                    (QVars (mempty & at "a" ?~ mempty))
                    (QVars (mempty & at "c" ?~ RowConstraints (fromList ["t"]) mempty))
                )
            & Pure

main :: IO ()
main = defaultMain [alphaEqTest]
