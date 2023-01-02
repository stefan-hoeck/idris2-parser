module Main

import Hedgehog
import Test.Lex.Core

%default total

main : IO ()
main = test [Lex.Core.props]
