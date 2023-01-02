module Main

import Test.Lex.Idris2.Common
import Test.Lex.Idris2.Package
import Hedgehog

%default total

main : IO ()
main = test [
    Common.props
  , Package.props
  ]
