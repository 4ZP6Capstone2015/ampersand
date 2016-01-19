{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-} 

module Database.Design.Ampersand.ECA2SQL.PrettyPrinterSQL () where

import Text.PrettyPrint.Leijen hiding ((<$>)) 
import Language.SQL.SimpleSQL.Syntax
import Language.SQL.SimpleSQL.Pretty
import Database.Design.Ampersand.ECA2SQL.TypedSQL hiding (PAclause(Ref))
import Database.Design.Ampersand.ECA2SQL.Singletons
import Database.Design.Ampersand.Core.AbstractSyntaxTree (ECArule(..))
import Database.Design.Ampersand.ECA2SQL.Utils 
import Data.List (intercalate,intersperse)
import Data.List.Utils (replace)
import Data.Char (toUpper)

instance Pretty ECArule where 

instance Pretty (SQLSt k v) where
    pretty (Insert tableSpec_ expr2ins) = text "INSERT INTO" <+> showTableSpec tableSpec_ <+> text "VALUES " <+> lparen  <+> showSQLVal expr2ins <+> rparen 
    pretty (Delete tableSpec_ from) = foldl1 (<>) 
      [ text "DELETE FROM" 
      , showTableSpec tableSpec_
      , text " WHERE " 
      , withSingT (typeOfTableSpec tableSpec_) $ \_ -> prettySQLFromClause from
      ]
    pretty x = case x of 
     {  IfSQL cnd t0 t1 -> 
                          text "SELECT IF" <> lparen <> (showSQLVal cnd) <> text "," <> pretty t0 <> text "," <> pretty t1 <> rparen;
        Update tb to arg -> withSingT (typeOfTableSpec tb) $ \_ -> 
                            text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg);
        -- Delete tb from -> withSingT (typeOfTableSpec tb) $ \_ -> 
                            -- text "DELETE FROM" <> (prettySQLFromClause from) <> text "WHERE" <> (showTableSpec tb);
        SetRef (Ref_ var) exp' -> text "SET @" <> (prettyNametoDoc var) <> text "=" <> (showSQLVal exp');
        DropTable tb -> text "DROP TABLE" <> (showTableSpec tb);
        MakeTable tbl -> 
                       text "CREATE TABLE" <> maketable tbl <> lparen <> maketable tbl <> text "," <> maketable tbl <> rparen -- need to find (col_ name, col_type)
      }
        -- _:>>= _
        -- YT: this is wrong! Read the comments on NewRef 
        -- NewRef tb a b -> text "SET"<> (newRefOne tb) <> text "\n" <> (newRefOne tb) <> text ":" <> text "\n\t" <> text "=" <> (prettyNewRef b);
        -- newRef takes string argument, its a maybe string a suggested name for the fresh name; string for semantic name


    {-Update tb to arg -> text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg);
      SetRef (Ref_ var) exp -> text "SET @" <> (prettyNametoDoc var) <> text "=" <> (showSQLVal exp);
        -}
    
--Update tableSpec to arg -> text "UPDATE" <> (showTableSpec tableSpec) <> text " SET " <> (prettySQLToClause to arg)

showSQLVal :: SQLVal a -> Doc
showSQLVal (SQLScalarVal x) = text $ prettyValueExpr theDialect x
showSQLVal (SQLQueryVal x) = text $ prettyQueryExpr theDialect x

-- pretty (Delete ..)
showTableSpec :: TableSpec t -> Doc
showTableSpec (MkTableSpec (Ref name)) = text $ getName name
showTableSpec (TableAlias_ _ t) = showTableSpec t 

--case for delete predicate
prettySQLFromClause :: forall ts . (Sing ('SQLRow ts)) => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> Doc -- ts is list of named types
prettySQLFromClause = prettySQLAtoB 
  -- showSQLVal $ f (SQLQueryVal (Table [UQName "Unique"]) :: SQLVal ('SQLRow ts))

--maketable :: SQLTypeS ('SQLRow t) -> Doc
maketable = error "TODO"
-- maketable = text $ prettyQueryExpr theDialect

prettyNametoDoc :: Name -> Doc
prettyNametoDoc = text . getName

prettySQLToClause:: (Sing ('SQLRow ts)) => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> (SQLVal ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> Doc
prettySQLToClause f g = prettySQLAtoB f <> text "TO" <> prettySQLAtoB g 

prettySQLAtoB :: forall a b . Sing a => (SQLVal a -> SQLVal b) -> Doc
prettySQLAtoB fn = 
  let inp = elimSingT (isScalarType (sing :: SingT a)) $ \case 
              WTrue  -> SQLScalarVal $ Iden [UQName "Unique"]
              WFalse -> SQLQueryVal $ Table [UQName "Unique"]
      inp :: SQLVal a 
  in showSQLVal $ fn inp 

--- [TODO ENDS]

getName x = prettyValueExpr theDialect $ Iden [x]

theDialect :: Dialect 
theDialect = MySQL
