module Main

import Lexer
import Parser
import Hedgehog

main : IO ()
main = test [ Lexer.props, Parser.props ]
