{-# OPTIONS_GHC -fno-warn-orphans #-}
module Database.Design.Ampersand.ECA2SQL.PrettyPrinterSQL
where

import Text.PrettyPrint.Leijen 
import Language.SQL.SimpleSQL.Syntax
import Language.SQL.SimpleSQL.Pretty
import Database.Design.Ampersand.ECA2SQL.TypedSQL
import Data.List (intercalate,intersperse)
import Data.List.Utils (replace)
import Data.Char (toUpper)

--TableSpec ts -> SQLVal ('SQLRel ('SQLRow ts))
instance Pretty (SQLSt k v) where
    pretty (Insert tableSpec expr2ins) = text "INSERT INTO" <+> (text ts) <+> text "VALUES " <+> lparen  <+> (text vals) <+> rparen 
        where ts = showTableSpec tableSpec
              vals = showSQLRow expr2ins
   pretty x = case x of {
        Update tb to arg -> text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg)
		Delete tb from -> text "DELETE"  <> (prettySQLFromClause from) <> text "From" <> (showTableSpec tb)
   } 

   -- pretty (Delete ..)
showTableSpec :: TableSpec t -> String
showTableSpec (MkTableSpec (Ref name)) = getName name


showSQLRow :: SQLVal a -> String
showSQLRow (SQLScalarVal x) = (prettyValueExpr theDialect x)
showSQLRow (SQLQueryVal x) = (prettyQueryExpr theDialect x)

--[TODO : showSQLVal to String]
--showSQLVal :: SQLVal -> String

getName x = prettyValueExpr theDialect $ Iden [x]
theDialect :: Dialect 
theDialect = MySQL


prettySQLToClause:: (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> (SQLVal ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> Doc
prettySQLToClause = error "TODO"


prettySQLFromClause :: (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> Doc -- ts is list of named types
prettySQLFromClause = error "TODO"

prettySQLAtoB :: (SQLVal a -> SQLVal b) -> Doc
prettySQLAtoB = errror "TODO" -- look at SQLVal, find how to get it to doc