module Test.Lex.Util

import public Text.Lex
import public Text.Bounded as B
import public Libraries.Text.Lexer
import public Hedgehog

%default total

public export
0 ILexer : Type
ILexer = Libraries.Text.Lexer.Core.Lexer

public export
0 PLexer : Type
PLexer = Text.Lex.Core.Lexer

public export
0 ITokenMap : Type -> Type
ITokenMap = Libraries.Text.Lexer.Core.TokenMap

public export
0 PTokenMap : Type -> Type
PTokenMap = Text.Lex.Core.TokenMap Char

public export
0 IBounds : Type
IBounds = Libraries.Text.Bounded.Bounds

public export
0 PBounds : Type
PBounds = B.Bounds

public export
0 IBounded : Type -> Type
IBounded = Libraries.Text.Bounded.WithBounds

public export
0 PBounded : Type -> Type
PBounded = B.Bounded

export
toBounds : IBounds -> PBounds
toBounds (MkBounds sl sc el ec) =
  BS (P (cast sl) (cast sc)) (P (cast el) (cast ec))

export
toWithBounds : IBounded a -> PBounded a
toWithBounds (MkBounded val False bs) = B val $ toBounds bs
toWithBounds (MkBounded val True bs) = B val NoBounds

toLexRes :
     (List (IBounded a), (Int,Int,String))
  -> (SnocList (PBounded a), (Position,List Char))
toLexRes (bs, (l,c,s)) =
  (Lin <>< map toWithBounds bs, (P (cast l) (cast c), unpack s))

toLexRes' :
     TokRes False s r a
  -> (SnocList (PBounded a), (Position,List Char))
toLexRes' (TR pos res reason rem prf) = (res, pos, rem)

export
testTokenLex :
     Monad m
  => Eq a
  => Show a
  => (s    : String)
  -> (pmap : PTokenMap a)
  -> (imap : ITokenMap a)
  -> {auto 0 p : NonEmpty pmap}
  -> TestT m ()
testTokenLex s pmap imap =
  let res1 := Text.Lex.Tokenizer.lex (Direct $ first pmap) s
      res2 := Libraries.Text.Lexer.Core.lex imap s
   in toLexRes' res1 === toLexRes res2

export %inline
testLex :
     Monad m
  => (s     : String)
  -> (lex   : Text.Lex.Core.Lexer)
  -> (lexer : Libraries.Text.Lexer.Core.Lexer)
  -> TestT m ()
testLex s lex lexer = testTokenLex s [(lex, cast)] [(lexer, id)]
