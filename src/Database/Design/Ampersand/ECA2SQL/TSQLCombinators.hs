{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ( module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ) where 

import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import Database.Design.Ampersand.ECA2SQL.Utils 
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Prelude (undefined, ($), Bool(..)) -- This module is intended to be imported qualified

true :: SQLVal 'SQLBool
true = unsafeSQLVal $ Sm.In True (Sm.NumLit "0") $ Sm.InList [Sm.NumLit "0"]

false :: SQLVal 'SQLBool
false = unsafeSQLVal $ Sm.In True (Sm.NumLit "1") $ Sm.InList [Sm.NumLit "0"]

not :: SQLVal 'SQLBool -> SQLVal 'SQLBool
not x = unsafeSQLVal $ Sm.PrefixOp ["NOT"] $ elimSQLVal x 

in_, notIn :: forall a . (IsScalarType a ~ True) => SQLVal a -> SQLVal ('SQLRel a) -> SQLVal 'SQLBool
in_ x y = unsafeSQLVal $ Sm.In True (elimSQLVal x) (Sm.InQueryExpr $ elimSQLVal y) 
notIn x y = unsafeSQLVal $ Sm.In False (elimSQLVal x) (Sm.InQueryExpr $ elimSQLVal y) 


-- g_binOp :: SQLVal
