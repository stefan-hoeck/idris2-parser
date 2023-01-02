module Core.Name.Namespace.Extra

import Data.List1
import public Core.Name.Namespace

%default total

splitOnto :
     List Char
  -> List String
  -> SnocList Char
  -> List1 String
splitOnto xs ss (sx :< '.') = splitOnto [] (pack xs :: ss) sx
splitOnto xs ss (sx :< x)   = splitOnto (x :: xs) ss sx
splitOnto xs ss [<]         = pack xs ::: ss

export
mkNamespacedIdent : SnocList Char -> (Maybe Namespace, String)
mkNamespacedIdent cs =
  let name ::: ns = reverse (splitOnto [] [] cs)
   in case ns of
     [] => (Nothing, name)
     _  => (Just (MkNS ns), name)
