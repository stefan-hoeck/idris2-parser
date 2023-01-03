module Text.Lex.Idris2.Common

import public Text.Lex

%hide Prelude.(<+>)
%default total

||| In `comment` we are careful not to parse closing delimiters as
||| valid comments. i.e. you may not write many dashes followed by
||| a closing brace and call it a valid comment.
export
comment : Lexer
comment = linefeedComment $ is '-' <+> preds (== '-') <+> reject (is '}')

public export
data Flavour = AllowDashes | Capitalised | Normal

isIdentStart : Flavour -> Char -> Bool
isIdentStart _           '_' = True
isIdentStart Capitalised  x  = isUpper x || x > chr 160
isIdentStart _            x  = isAlpha x || x > chr 160

isIdentTrailing : Flavour -> Char -> Bool
isIdentTrailing AllowDashes '-'  = True
isIdentTrailing _           '\'' = True
isIdentTrailing _           '_'  = True
isIdentTrailing _            x   = isAlphaNum x || x > chr 160

export %inline
isIdent : Flavour -> String -> Bool
isIdent fl str = case unpack str of
  []    => False
  x::xs => isIdentStart fl x && all (isIdentTrailing fl) xs

export %inline
ident : Flavour -> Lexer
ident fl = pred (isIdentStart fl) <+> preds0 (isIdentTrailing fl)

export
isIdentNormal : String -> Bool
isIdentNormal = isIdent Normal

export
identNormal : Lexer
identNormal = ident Normal

export
identAllowDashes : Lexer
identAllowDashes = ident AllowDashes

namespaceIdent : Lexer
namespaceIdent = ident Capitalised <+> many (is '.' <+> ident Capitalised <+> expect (is '.'))

export
namespacedIdent : Lexer
namespacedIdent = namespaceIdent <+> opt (is '.' <+> identNormal)
