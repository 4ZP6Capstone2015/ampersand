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

    pretty (Insert tableSpec expr2ins) = text "INSERT INTO" <+> ts <+> text "VALUES " <+> lparen  <+> vals <+> rparen 
        where ts = showTableSpec tableSpec
              vals = showSQLRow expr2ins
    pretty x = case x of 
    {
        Update tb to arg -> text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg);
        Delete tb from -> text "DELETE" <> (prettySQLFromClause from) <> text "From" <> (showTableSpec tb);
        SetRef (Ref_ var) exp -> text "SET @" <> (prettyNametoDoc var) <> text "=" <> (showSQLRow exp);
        DropTable tb -> text "DROP TABLE" <> (showTableSpec tb);
        NewRef tb a b -> text "SET"<> (newRefOne tb) <> text "\n" <> (newRefOne tb) <> text ":" <> text "\n\t" <>(newRefTwo a) <> text "=" <> (prettyNewRef b);
		-- MakeTable tbl
		-- Insert _ _
		-- IfSQL _ _ _
		-- _:>>= _
    }

-- pretty (Delete ..) <-- why is this here?
showTableSpec :: TableSpec t -> Doc
showTableSpec mktspec = case mktspec of 
    (MkTableSpec (Ref name)) -> text (show(getName name))

newRefOne :: SQLTypeS a1 -> Doc
newRefOne = error "TODO"

newRefTwo :: Maybe String -> Doc
newRefTwo = error "TODO"

showSQLRow :: SQLVal a -> String
showSQLRow (SQLScalarVal x) = prettyValueExpr theDialect x
showSQLRow (SQLQueryVal x) = prettyQueryExpr theDialect x

-- pretty (Delete ..)
showTableSpec :: TableSpec t -> String
showTableSpec (MkTableSpec (Ref name)) = getName name


--case for delete predicate
prettySQLFromClause :: forall ts . Sing ts => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> String -- ts is list of named types
prettySQLFromClause f = showSQLRow $ f (SQLQueryVal (Table [UQName "Unique"]) :: SQLVal ('SQLRow ts)) 


prettyNewRef :: Maybe (SQLVal a1) -> Doc
prettyNewRef = error "TODO"

getName x = prettyValueExpr theDialect $ Iden [x]
theDialect :: Dialect 
theDialect = MySQL


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
