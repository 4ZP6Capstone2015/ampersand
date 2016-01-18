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