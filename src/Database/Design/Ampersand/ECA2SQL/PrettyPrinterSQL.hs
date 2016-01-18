{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-} 

module Database.Design.Ampersand.ECA2SQL.PrettyPrinterSQL
where

import Text.PrettyPrint.Leijen 
import Language.SQL.SimpleSQL.Syntax
import Language.SQL.SimpleSQL.Pretty
import Database.Design.Ampersand.ECA2SQL.TypedSQL
import Database.Design.Ampersand.ECA2SQL.Singletons
import Data.List (intercalate,intersperse)
import Data.List.Utils (replace)
import Data.Char (toUpper)

instance Pretty (SQLSt k v) where

    pretty (Insert tableSpec_ expr2ins) = text "INSERT INTO" <+> (text $ showTableSpec tableSpec_) <+> text "VALUES " <+> lparen  <+> (text $ showSQLRow expr2ins) <+> rparen 
    pretty (Delete tableSpec_ from) = text "DELETE FROM" <> (text $ showTableSpec tableSpec_)  <> text " WHERE " <> (text $ prettySQLFromClause from)
    {-Update tb to arg -> text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg);
      SetRef (Ref_ var) exp -> text "SET @" <> (prettyNametoDoc var) <> text "=" <> (showSQLRow exp);
        -}
    
--Update tableSpec to arg -> text "UPDATE" <> (showTableSpec tableSpec) <> text " SET " <> (prettySQLToClause to arg)

showSQLRow :: SQLVal a -> String
showSQLRow (SQLScalarVal x) = prettyValueExpr theDialect x
showSQLRow (SQLQueryVal x) = prettyQueryExpr theDialect x

-- pretty (Delete ..)
showTableSpec :: TableSpec t -> String
showTableSpec (MkTableSpec (Ref name)) = getName name


--case for delete predicate
prettySQLFromClause :: forall ts . Sing ts => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> String -- ts is list of named types
prettySQLFromClause f = showSQLRow $ f (SQLQueryVal (Table [UQName "Unique"]) :: SQLVal ('SQLRow ts)) 
 

--[TODO PART BELOW]

prettyNametoDoc :: Name -> Doc
prettyNametoDoc = error "TODO"
prettySQLToClause:: (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> (SQLVal ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> Doc
prettySQLToClause = error "TODO"


prettySQLAtoB :: (SQLVal a -> SQLVal b) -> Doc

prettySQLAtoB = error "TODO" -- look at SQLVal, find how to get it to doc
--- [TODO ENDS]

getName x = prettyValueExpr theDialect $ Iden [x]

theDialect :: Dialect 
theDialect = MySQL
