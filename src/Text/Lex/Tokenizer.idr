module Text.Lex.Tokenizer

import Derive.Prelude
import public Text.Lex

%default total
%language ElabReflection

||| Description of a language's tokenization rule.
public export
data Tokenizer : (charType, tokenType : Type) -> Type where
  Match :
       {0 charType, tokenType : Type}
    -> Recognise True charType
    -> (SnocList charType -> tokenType)
    -> Tokenizer charType tokenType

  Compose :
       {0 charType, tokenType, tag : Type}
    -> (begin    : Recognise True charType)
    -> (mapBegin : SnocList charType -> tokenType)
    -> (tagger   : SnocList charType -> tag)
    -> (middle   : Inf (tag -> Tokenizer charType tokenType))
    -> (end      : tag -> Recognise True charType)
    -> (mapEnd   : SnocList charType -> tokenType)
    -> Tokenizer charType tokenType

  (<|>) :
       {0 charType, tokenType : Type}
    -> Tokenizer charType tokenType
    -> Lazy (Tokenizer charType tokenType)
    -> Tokenizer charType tokenType

||| Stop reason why tokenizer can't make more progress.
||| @ ComposeNotClosing carries the span of composition begin token in the
|||                     form of `(startLine, startCol), (endLine, endCol)`.
public export
data StopReason =
    EndInput
  | NoRuleApply
  | ComposeNotClosing (Nat, Nat) (Nat, Nat)

%runElab derive "StopReason" [Show, Eq]

public export
record TokStep (a : Type) (cs : List Char) where
  constructor ST
  line  : Nat
  col   : Nat
  res   : SnocList (WithBounds a)
  rem   : List Char
  0 prf : Suffix True rem cs


tokenise :
     (reject    : Lexer)
  -> (tokenizer : Tokenizer Char a)
  -> (line, col : Nat)
  -> (toks      : SnocList (WithBounds a))
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> (SnocList (WithBounds a), (StopReason, Nat, Nat, List Char))

tokenise _   _ l c ts [] _                = (ts, EndInput, (l, c, []))
tokenise rej t l c ts cs acc@(Access rec) = case run rej [<] cs of
  Res _ _ _ => (ts, EndInput, (l,c,cs))
  Stop      => case next t cs acc of
    Right (ST l2 c2 ts2 cs2 p) => tokenise rej t l2 c2 ts2 cs2 (rec cs2 p)
    Left r => (ts, (r, l, c, cs))
  where
    next :
         Tokenizer Char a
      -> (cs    : List Char)
      -> (0 acc : SuffixAcc cs)
      -> Either StopReason (TokStep a cs)

    next (Match x f) cs _ = case step l c x f cs of
      Just (ST l2 c2 res rem p)  => Right (ST l2 c2 (ts :< res) rem p)
      Nothing => Left NoRuleApply
    next (Compose b mapb tagger midFn endFn mapEnd) cs (Access rec) =
      let Just (ST l2 r2 sc cs2 p) := step l c b id cs
            | Nothing => Left NoRuleApply
          tag    := tagger sc.val
          middle := midFn tag
          end    := endFn tag
          (midToks, (reason, l3, c3, 
       in ?foo
    --     getFirstMatch (Compose begin mapBegin tagger middleFn endFn mapEnd) str
    --         = let Just (beginTok', line', col' , rest) = getNext begin line col str
    --                 | Nothing => Left NoRuleApply
    --               tag = tagger beginTok'
    --               middle = middleFn tag
    --               end = endFn tag
    --               beginTok'' = MkBounded (mapBegin beginTok') False (MkBounds line col line' col')
    --               (midToks, (reason, line'', col'', rest'')) =
    --                     assert_total $ tokenise end middle line' col' [] rest
    --            in case reason of
    --                    (ComposeNotClosing _ _) => Left reason
    --                    _ => let Just (endTok', lineEnd, colEnd, restEnd) =
    --                                 getNext end line'' col'' rest''
    --                               | _ => Left $ ComposeNotClosing (line, col) (line', col')
    --                             endTok'' = MkBounded (mapEnd endTok') False (MkBounds line'' col'' lineEnd colEnd)
    --                          in Right ([endTok''] ++ reverse midToks ++ [beginTok''], lineEnd, colEnd, restEnd)
    next (x <|> y) cs acc = case next x cs acc of
      Right res => Right res
      Left  r@(ComposeNotClosing {}) => Left r
      Left  _                        => next y cs acc

-- 
-- export
-- lexTo : Lexer ->
--         Tokenizer a ->
--         String ->
--         (List (WithBounds a), (StopReason, Int, Int, String))
-- lexTo reject tokenizer str
--     = let (ts, reason, (l, c, str')) =
--               tokenise reject tokenizer 0 0 [] (fastUnpack str) in
--           (ts, reason, (l, c, fastPack str'))
-- 
-- ||| Given a tokenizer and an input string, return a list of recognised tokens,
-- ||| and the line, column, and remainder of the input at the first point in the string
-- ||| where there are no recognised tokens.
-- export
-- lex : Tokenizer a -> String -> (List (WithBounds a), (StopReason, Int, Int, String))
-- lex tokenizer str = lexTo (pred $ const False) tokenizer str
