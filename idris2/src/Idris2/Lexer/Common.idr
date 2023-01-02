module Idris2.Lexer.Common

import Text.Lex

%hide Prelude.(<+>)
%default total

||| In `comment` we are careful not to parse closing delimiters as
||| valid comments. i.e. you may not write many dashes followed by
||| a closing brace and call it a valid comment.
export
comment : Lexer
comment = lineComment $ is '-' <+> preds (== '-') <+> reject (is '}')
