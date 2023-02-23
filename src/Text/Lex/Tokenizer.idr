module Text.Lex.Tokenizer

import Derive.Prelude
import Text.ParseError
import Text.Bounds
import Text.Lex.Manual

%default total

||| Description of a language's tokenization rule.
public export
data Tokenizer : (charType, tokenType : Type) -> Type where
  ||| Use this for fast, direct lexing of constant tokens.
  ||| Note: It is assumed that the lexed characters do *NOT* contain
  ||| any line breaks.
  Direct : {0 ct,tt : _} -> Tok ct tt -> Tokenizer ct tt

  Compose :
       {0 ct, tt, tag : Type}
    -> (begin    : Tok ct (tt, tag))
    -> (middle   : Inf (tag -> Tokenizer ct tt))
    -> (end      : tag -> Tok ct tt)
    -> Tokenizer ct tt

  (<|>) :
       {0 ct, tt : Type}
    -> Tokenizer ct tt
    -> Lazy (Tokenizer ct tt)
    -> Tokenizer ct tt

export
choiceMap :
     (a -> Tokenizer ct tt)
  -> (as : List a)
  -> {auto 0 prf : NonEmpty as}
  -> Tokenizer ct tt
choiceMap f (h :: t) = foldl (\v,e => v <|> f e) (f h) t

export %inline
choice :
     (rs : List $ Tokenizer ct tt)
  -> {auto 0 prf : NonEmpty rs}
  -> Tokenizer ct tt
choice rs = choiceMap id rs

||| Result of running a `Tokenizer` repeatedly over a
||| sequence of characters.
public export
record TokRes (strict : Bool) (cs : List Char) r a where
  constructor TR
  pos    : Position
  toks   : SnocList (Bounded a)
  reason : Maybe r 
  rem    : List Char
  0 suf  : Suffix strict rem cs

wtrans : TokRes False cs r a -> (0 y : Suffix True cs xs) -> TokRes False xs r a
wtrans (TR x sx r rem z) y = TR x sx r rem (weaken $ trans z y)

tokenise :
     (tokenizer : Tokenizer Char a)
  -> Position
  -> (toks    : SnocList (Bounded a))
  -> (cs      : List Char)
  -> (0 acc   : SuffixAcc cs)
  -> TokRes False cs (Bounded $ ParseError a e) a
tokenise x pos toks [] _ = TR pos toks Nothing [] Same
tokenise x pos toks cs acc@(SA r) = case next x cs acc of
  Right (TR pos2 toks2 Nothing cs2 su) =>
    tokenise x pos2 toks2 cs2 r `wtrans` su
  Left y  => TR pos toks (Just y) cs Same
  where
    next :
         Tokenizer Char a
      -> (cs    : List Char)
      -> (0 acc : SuffixAcc cs)
      -> Either (Bounded $ ParseError a e) (TokRes True cs Void a)
    next (Direct f) cs _ = case f cs of
      Succ val xs     @{p} =>
        let pos2 := endPos pos p
         in Right (TR pos2 (toks :< bounded val pos pos2) Nothing xs p)
      Fail start errEnd r =>
        Left $ boundedErr pos start errEnd (Reason r)
    next (Compose beg midFn endFn) cs acc@(SA r) = case beg cs of
      Fail start errEnd r =>
        Left $ boundedErr pos start errEnd (Reason r)
      Succ (st,tg) cs2 @{p2} =>
        let pos2   := endPos pos p2
            middle := midFn tg
            end    := endFn tg
            toks2  := toks :< bounded st pos pos2
            TR pos3 toks3 r cs3 p3 := tokenise middle pos2 toks2 cs2 r
         in case r of
              Just r@(B (Unclosed _) _) => Left r
              _                         => case end cs3 of
                Succ val cs4 @{p4}   =>
                  let pos4   := endPos pos3 p4
                      toks4  := toks3 :< bounded val pos3 pos4
                   in Right (TR pos4 toks4 Nothing cs4 $ trans p4 (trans p3 p2))
                Fail start errEnd y => case y of
                  EOI => Left $ boundedErr pos start errEnd (Unclosed st)
                  r    => Left $ boundedErr pos start errEnd (Reason r)
    next (x <|> y) cs acc = case next x cs acc of
      Right res                  => Right res
      Left  r@(B (Unclosed _) _) => Left r
      Left  _                    => next y cs acc

||| Given a tokenizer and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the string
||| where there are no recognised tokens.
export %inline
lex :
     Tokenizer Char a
  -> (s : String)
  -> TokRes False (unpack s) (Bounded $ ParseError a Void) a
lex x s = tokenise x begin [<] (unpack s) suffixAcc
