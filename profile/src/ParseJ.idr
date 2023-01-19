module ParseJ

import Data.List.Quantifiers
import JSON
import LexJSON
import Text.Lex.Bounded

%default total

data ArrTag = AEmpty | AVals | AComma

data ObjTag = OEmpty | OVals | HasString | OComma

data Tag = Arr ArrTag | Obj ObjTag

0 TagType : Tag -> Type
TagType (Arr _)          = SnocList JSON
TagType (Obj HasString)  = (String, SnocList (String,JSON))
TagType (Obj _)          = (SnocList (String,JSON))

record State where
  constructor ST
  tags   : List Tag
  states : All TagType tags

data Res : Type where
  Done  : JSON -> Res
  Ready : State -> Res
  Err   : Res

val : JSON -> State -> Res
val x (ST [] [])               = Done x
val x (ST (t :: ts) (s :: ss)) = case t of
  Arr AVals     => Err
  Arr _         => Ready $ ST (Arr AVals :: ts) ((s :< x) :: ss)
  Obj HasString => 
    let (str,sv) := s
     in Ready $ ST (Obj OVals :: ts) ((sv :< (str,x)) :: ss) 
  Obj _         => Err

opn : (x : Tag) -> (y : TagType x) -> State -> Res
opn x y (ST (t :: ts) (s :: ss)) = case t of
  Arr AVals     => Err
  Arr _         => Ready $ ST (x :: t :: ts) (y :: s :: ss)
  Obj HasString => Ready $ ST (x :: t :: ts) (y :: s :: ss) 
  Obj _         => Err
opn x y (ST [] []) = Ready $ ST [x] [y]

arrClose : State -> Res
arrClose (ST (Arr AEmpty :: ts) (s :: ss)) = val (JArray $ s <>> []) (ST ts ss)
arrClose (ST (Arr AVals :: ts) (s :: ss))  = val (JArray $ s <>> []) (ST ts ss)
arrClose _                                 = Err

objClose : State -> Res
objClose (ST (Obj OEmpty :: ts) (s :: ss)) = val (JObject $ s <>> []) (ST ts ss)
objClose (ST (Obj OVals :: ts) (s :: ss))  = val (JObject $ s <>> []) (ST ts ss)
objClose _                                 = Err

objString : String -> State -> Res
objString str (ST (Obj OEmpty :: ts) (s :: ss)) =
  Ready $ ST (Obj HasString :: ts) ((str,s) :: ss)
objString str (ST (Obj OComma :: ts) (s :: ss)) =
  Ready $ ST (Obj HasString :: ts) ((str,s) :: ss)
objString _ _ = Err

comma : State -> Res
comma (ST (Arr AVals :: ts) (s :: ss)) = Ready $ ST (Arr AComma :: ts) (s :: ss)
comma (ST (Obj OVals :: ts) (s :: ss)) = Ready $ ST (Obj OComma :: ts) (s :: ss)
comma _ = Err

go : Res -> List (Bounded Tok) -> Maybe (JSON, List $ Bounded Tok)
go (Ready s) xs = case xs of
  MkBounded (TLit $ JString l) _ :: MkBounded TColon _ :: t => go (objString l s) t
  h :: t => case h.val of
    TBracketO => go (opn (Arr AEmpty) [<] s) t
    TBracketC => go (arrClose s) t
    TBraceO   => go (opn (Obj OEmpty) [<] s) t
    TBraceC   => go (objClose s) t
    TComma    => go (comma s) t
    TLit x    => go (val x s) t
    TColon    => Nothing
  []                 => Nothing
go (Done x) xs  = Just (x,xs)
go Err _        = Nothing

export
stateParse : String -> Maybe JSON
stateParse str = case json str of
  (ts,l,c,[]) => case go (Ready $ ST [] []) (ts <>> []) of
    Just (j,[]) => Just j
    _           => Nothing
  (_,l,c,_) => Nothing

