module Text.Lex.Tokenizer

import Derive.Prelude
import Text.Lex.Core

%default total
%language ElabReflection

public export
data DirectRes : List Char -> Type -> Type where
  Succ :
      t
   -> (cs : List Char)
   -> {auto prf : Tail True cs cs'}
   -> DirectRes cs' t
  Fail : DirectRes cs t

||| Description of a language's tokenization rule.
public export
data Tokenizer : (tokenType : Type) -> Type where
  ||| Use this for fast, direct lexing of constant tokens.
  ||| Note: It is assumed that the lexed characters do *NOT* contain
  ||| any line breaks.
  Direct : ((cs : List Char) -> DirectRes cs t) -> Tokenizer t

  Match  : TokenMap t -> Tokenizer t

  Compose :
       {0 tokenType, tag : Type}
    -> (begin    : Recognise True Char)
    -> (mapBegin : SnocList Char -> tokenType)
    -> (tagger   : SnocList Char -> tag)
    -> (middle   : Inf (tag -> Tokenizer tokenType))
    -> (end      : tag -> Recognise True Char)
    -> (mapEnd   : SnocList Char -> tokenType)
    -> Tokenizer tokenType

  (<|>) :
       {0 tokenType : Type}
    -> Tokenizer tokenType
    -> Lazy (Tokenizer tokenType)
    -> Tokenizer tokenType

export
choiceMap :
     (a -> Tokenizer b)
  -> (as : List a)
  -> {auto 0 prf : NonEmpty as}
  -> Tokenizer b
choiceMap f (h :: t) = foldl (\v,e => v <|> f e) (f h) t

export %inline
choice :
     (rs : List $ Tokenizer b)
  -> {auto 0 prf : NonEmpty rs}
  -> Tokenizer b
choice rs = choiceMap id rs

||| Stop reason why tokenizer can't make more progress.
||| @ ComposeNotClosing carries the span of composition begin token in the
|||                     form of `(startLine, startCol), (endLine, endCol)`.
public export
data StopReason =
    EndInput
  | NoRuleApply
  | ComposeNotClosing Bounds

%runElab derive "StopReason" [Show, Eq]

||| Result of running a `Tokenizer` repeatedly over a
||| sequence of characters.
public export
record TokRes (strict : Bool) (cs : List Char) (r,a : Type) where
  constructor TR
  line   : Nat
  col    : Nat
  res    : SnocList (WithBounds a)
  reason : r
  rem    : List Char
  0 prf  : Suffix strict rem cs

mapPrf :
     {0 cs1,cs2 : List Char}
  -> (0 f :
          {cs : List Char}
       -> Suffix b1 cs cs1
       -> Suffix b2 cs cs2
     )
  -> TokRes b1 cs1 r a
  -> TokRes b2 cs2 r a
mapPrf f (TR l c res r rem prf) = TR l c res r rem (f prf)

%inline
(~?>) : TokRes b1 cs1 r a -> (0 p : Suffix b2 cs1 cs2) -> TokRes False cs2 r a
r ~?> p = mapPrf (\q => weaken $ trans q p) r

tokenise :
     (reject    : Lexer)
  -> (tokenizer : Tokenizer a)
  -> (line, col : Nat)
  -> (toks      : SnocList (WithBounds a))
  -> (cs        : List Char)
  -> (0 acc : SuffixAcc cs)
  -> TokRes False cs StopReason a
tokenise _   _ l c ts [] _                = TR l c ts EndInput [] Same
tokenise rej t l c ts cs acc@(Access rec) = case run rej [<] cs of
  Res _ _ _ => TR l c ts EndInput cs Same
  Stop      => case next t cs acc of
    Right (TR l2 c2 ts2 _ cs2 p) =>
      tokenise rej t l2 c2 ts2 cs2 (rec cs2 p) ~?> p
    Left r => TR l c ts r cs Same
  where
    next :
         Tokenizer a
      -> (cs    : List Char)
      -> (0 acc : SuffixAcc cs)
      -> Either StopReason (TokRes True cs () a)
    next (Direct f) cs _ = case f cs of
      Succ x ds @{sfx} => 
        let c2  := c + tailToNat sfx
            res := MkBounded x $ Just (MkBounds l c l c2)
         in Right (TR l c2 (ts :< res) () ds $ suffix sfx)
      Fail      => Left NoRuleApply
    next (Match m) cs _ = case first l c m cs of
      Just (ST l2 c2 res rem p)  => Right (TR l2 c2 (ts :< res) () rem p)
      Nothing => Left NoRuleApply
    next (Compose b mapb tagger midFn endFn mapEnd) cs (Access rec) =
      let Just (ST l2 c2 sc cs2 p2) := step l c b id cs
            | Nothing => Left NoRuleApply
          tag      := tagger sc.val
          middle   := midFn tag
          end      := endFn tag
          beginTok := map mapb sc
          TR l3 c3 midToks reason cs3 p3 :=
            tokenise end middle l2 c2 (ts :< beginTok) cs2 (rec cs2 p2)
       in case reason of
         ComposeNotClosing {} => Left reason
         _                    =>
           case step l3 c3 end mapEnd cs3 of
             Just (ST l4 c4 resEnd cs4 p4) =>
               Right (TR l4 c4 (midToks :< resEnd) () cs4 $ p4 ~> p3 ~> p2)
             Nothing => Left (ComposeNotClosing $ MkBounds l c l2 c2)
    next (x <|> y) cs acc = case next x cs acc of
      Right res => Right res
      Left  r@(ComposeNotClosing {}) => Left r
      Left  _                        => next y cs acc

export %inline
lexTo :
     Lexer
  -> Tokenizer a
  -> (s : String)
  -> TokRes False (unpack s) StopReason a
lexTo rej x s = tokenise rej x 0 0 [<] (unpack s) (ssAcc _)

||| Given a tokenizer and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the string
||| where there are no recognised tokens.
export %inline
lex : Tokenizer a -> (s : String) -> TokRes False (unpack s) StopReason a
lex = lexTo stop
