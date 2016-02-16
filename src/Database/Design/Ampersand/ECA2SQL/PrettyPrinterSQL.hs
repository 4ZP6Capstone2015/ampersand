{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-} 

module Database.Design.Ampersand.ECA2SQL.PrettyPrinterSQL (eca2PrettySQL) where

import Text.PrettyPrint.Leijen hiding ((<$>)) 
import Language.SQL.SimpleSQL.Syntax hiding (Statement(..))
import Language.SQL.SimpleSQL.Pretty
import Database.Design.Ampersand.ECA2SQL.TypedSQL -- hiding (PAclause(Ref))
import Database.Design.Ampersand.ECA2SQL.Singletons
import Database.Design.Ampersand.Core.AbstractSyntaxTree (ECArule(..))
import Database.Design.Ampersand.FSpec(FSpec)
import Database.Design.Ampersand.ECA2SQL.Utils 
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as TSQL 
import Database.Design.Ampersand.ECA2SQL (eca2SQL)
import Data.List (intercalate,intersperse)
import Data.List.Utils (replace)
import Data.Char (toUpper)
import Data.Coerce 
import Debug.Trace (trace) 

instance IsString Doc where 
  fromString = text 


eca2PrettySQL :: FSpec -> ECArule -> Doc 
eca2PrettySQL fs eca = pretty (nm, eca2SQL fs eca)
  where nm = "ecaRule" ++ show (ecaNum eca)
      

instance {-# OVERLAPPABLE #-} (x ~ String) => Pretty (x, SQLMethod args out) where
  pretty (paramName, SQLMethodWithFormalParams params mthd) =     
    vsep 
    [ "CREATE PROCEDURE" <+> text paramName <+> lparen <> ppParams <> rparen 
    , "BEGIN"
    , nest 4 (pretty mthd) 
    , "END" 
    ] where ppParams = foldlProd (empty :: Doc) (coerce h) params 
            h :: SQLValSem ('SQLRef q) -> Doc -> Doc
            h var@(GetRef varNm') = (<> text varNm <+> varTy) where 
              varNm = show varNm' 
              varTy = pretty $ typeOfSem var 
            h _ = error "pattern syn" 

  pretty (paramName, MkSQLMethod paramTys fun) = 
    pretty (paramName, SQLMethodWithFormalParams params (fun params))
      where params = mapProd mkParam $ sing2prod paramTys
            mkParam :: forall t . SingT t -> (:.:) SQLValSem 'SQLRef t
            mkParam ty = Cmp (unsafeRefFromName ty "param") 

instance Pretty (SQLTypeS x) where 
  pretty ty' = elimSingT ty' $ \case 
    WSQLBool -> "BOOL" 
    WSQLAtom -> "VARCHAR(255)" 
    _ -> error "pretty{SQLTypeS}:todo"

instance Pretty (SQLSt k v) where pretty = prettySqlSt
  

prettySqlSt :: SQLSt k v -> Doc 
prettySqlSt = fst . prettyRec

retUnit :: a -> (a, SQLValSem 'SQLUnit)
retUnit x = (x, Unit)

prettyRec :: SQLSt k v -> (Doc, SQLValSem v)
prettyRec (x :>>= f) = 
  case prettyRec x of 
    (ppr_x, val_x) -> 
      case prettyRec (f val_x) of 
        (ppr_fx, val_fx) -> (ppr_x <> ";" <$$> ppr_fx, val_fx)

prettyRec (Insert tableSpec_ expr2ins) = retUnit $ 
  text "INSERT INTO" <+> showTableSpec tableSpec_ <+> text "VALUES " <+> lparen  <+> showSQLVal expr2ins <+> rparen 

prettyRec (Delete tableSpec_ from) = retUnit $ foldl1 (<>) 
  [ text "DELETE FROM" 
  , showTableSpec tableSpec_
  , text " WHERE " 
  , withSingT (typeOfTableSpec tableSpec_) $ \_ -> prettySQLFromClause from
  ]
prettyRec (IfSQL cnd t0 t1) = 
  case prettyRec t0 of { (ppr_t0, _val_t0) -> 
  case prettyRec t1 of { (ppr_t1, _val_t1) -> retUnit $ 
    vsep                          
      [ text "IF" <> lparen <> showSQLVal cnd <> rparen <> text "THEN"   
      , indent 4 (ppr_t0 <> text ";")
      , indent (-4) (text "ELSE") 
      , indent 4 ppr_t1 
      ] 
    -- text "SELECT IF" <> lparen <> (showSQLVal cnd) <> text "," <> ppr_t0 <> text "," <> ppr_t1 <> rparen
  }}                         

prettyRec (Update tb to arg) = retUnit $ 
  withSingT (typeOfTableSpec tb) $ \_ -> 
  text "UPDATE" <> (showTableSpec tb) <> text "SET" <> (prettySQLToClause to arg)

prettyRec (SetRef (Ref_ var) exp') = retUnit $ 
  text "SET @" <> (prettyNametoDoc var) <> text "=" <> (showSQLVal exp')

prettyRec (DropTable tb) = retUnit $ text "DROP TABLE" <> (showTableSpec tb)

prettyRec (NewRef refTy mbRefNm mbRefVal) = 
  let refNm = maybe "ref" id mbRefNm
      refNmSem = unsafeRefFromName refTy $ Name Nothing refNm
  in ( text "SET @" <> text refNm <+> ":=" <+> maybe "NULL" pretty mbRefVal
     , refNmSem
     )

prettyRec SQLNoop = retUnit $ "SET @this_is_a_noop = 0"

prettyRec (SQLRet x) = ("RETURN" <+> pretty x,Val x)
prettyRec _ = error "prettyRec: not yet supported" 

instance Pretty (SQLVal a) where 
  pretty (SQLScalarVal x) = prettyValueExprDoc theDialect x
  pretty (SQLQueryVal x) = prettyQueryExprDoc theDialect x

showSQLVal :: SQLVal a -> Doc
showSQLVal = pretty 

-- pretty (Delete ..)
showTableSpec :: TableSpec t -> Doc
showTableSpec (MkTableSpec (GetRef name)) = text $ getName name
showTableSpec (TableAlias_ _ t) = showTableSpec t 

--case for delete predicate
prettySQLFromClause :: forall ts . (Sing ('SQLRow ts)) => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> Doc -- ts is list of named types
prettySQLFromClause = prettySQLAtoB 

  -- showSQLVal $ f (SQLQueryVal (Table [UQName "Unique"]) :: SQLVal ('SQLRow ts))



-- ifSQLfun :: SQLVal 'SQLBool -> Doc
-- ifSQLfun = error "TODO"

-- testing () = failure 
--[TODO PART BELOW]
--maketable :: SQLTypeS ('SQLRow t) -> Doc
-- maketable = text $ prettyQueryExpr theDialect

prettyNametoDoc :: Name -> Doc
prettyNametoDoc = text . getName

prettySQLToClause:: (Sing ('SQLRow ts)) => (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> (SQLVal ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> Doc
prettySQLToClause f g = prettySQLAtoB f <> text "TO" <> prettySQLAtoB g 

prettySQLAtoB :: forall a b . Sing a => (SQLVal a -> SQLVal b) -> Doc
prettySQLAtoB fn = 
  let inp = elimSingT (isScalarType (sing :: SingT a)) $ \case 
              WTrue  -> SQLScalarVal $ Iden [Name Nothing "Unique"]
              WFalse -> SQLQueryVal $ Table [Name Nothing "Unique"]
      inp :: SQLVal a 
  in showSQLVal $ fn inp 

--- [TODO ENDS]

getName x = prettyValueExpr theDialect $ Iden [x]

theDialect :: Dialect 
theDialect = mysql
