module Test.Lex.Util

import public Text.Lex
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
PTokenMap = Text.Lex.Core.TokenMap

public export
0 IBounds : Type
IBounds = Libraries.Text.Bounded.Bounds

public export
0 PBounds : Type
PBounds = Text.Lex.Bounded.Bounds

public export
0 IWithBounds : Type -> Type
IWithBounds = Libraries.Text.Bounded.WithBounds

public export
0 PWithBounds : Type -> Type
PWithBounds = Text.Lex.Bounded.WithBounds

export
toBounds : IBounds -> PBounds
toBounds (MkBounds sl sc el ec) =
  MkBounds (cast sl) (cast sc) (cast el) (cast ec)

export
toWithBounds : IWithBounds a -> PWithBounds a
toWithBounds (MkBounded val False bs) = MkBounded val $ Just $ toBounds bs
toWithBounds (MkBounded val True bs) = MkBounded val Nothing

toLexRes :
     (List (IWithBounds a), (Int,Int,String))
  -> (SnocList (PWithBounds a), (Nat,Nat,List Char))
toLexRes (bs, (l,c,s)) =
  (Lin <>< map toWithBounds bs, (cast l, cast c, unpack s))

toLexRes' :
     TokRes False s StopReason a
  -> (SnocList (PWithBounds a), (Nat,Nat,List Char))
toLexRes' (TR line col res reason rem prf) = (res, line, col, rem)

export
testTokenLex :
     Monad m
  => Eq a
  => Show a
  => (s    : String)
  -> (pmap : PTokenMap a)
  -> (imap : ITokenMap a)
  -> TestT m ()
testTokenLex s pmap imap =
  let res1 := Text.Lex.Tokenizer.lex (Match pmap) s
      res2 := Libraries.Text.Lexer.Core.lex imap s
   in toLexRes' res1 === toLexRes res2

export %inline
testLex :
     Monad m
  => (s     : String)
  -> (lex   : Text.Lex.Core.Lexer)
  -> (lexer : Libraries.Text.Lexer.Core.Lexer)
  -> TestT m ()
testLex s lex lexer = testTokenLex s [(lex, pack)] [(lexer, id)]
