module Main

import Hedgehog
import Props.Bool
import Props.Time

main : IO ()
main =
  test
    [ Bool.props
    , Time.props
    ]
