{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations, LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-}
import Control.Monad (unless)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
module Database.Design.Ampersand.ECA2SQL
  ( module Database.Design.Ampersand.ECA2SQL
  ) where
import Database.Design.Ampersand.Core.AbstractSyntaxTree
  ( ECArule(..), PAclause(..), Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
  , A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..), Signature(..)
  )
import Database.Design.Ampersand.FSpec (FSpec(..))
import Language.SQL.SimpleSQL.Syntax
  ( QueryExpr(..), ValueExpr(..), Name(..), TableRef(..), InPredValue(..), SubQueryExprType(..)
  , makeSelect
  )
import Database.Design.Ampersand.FSpec.FSpec (PlugSQL(..), PlugInfo(..), SqlAttribute(..), SqlAttributeUsage(..), SqlTType(SQLVarchar))
import Database.Design.Ampersand.FSpec.ToFSpec.ADL2Plug
import Database.Design.Ampersand.FSpec.SQL (expr2SQL,prettySQLQuery) --added Bin,to,Pretty
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils
import Database.Design.Ampersand.ECA2SQL.TypedSQL
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as T
import qualified GHC.TypeLits as TL
import Singletons


-- eca2SQLtest :: eca2SQL -> PAclause -> SQLValRef 'SQLBool -> SQLStatement 'SQLUnit
-- cant be proven without table, passes cabal type test repeatedly
-- can try test::State->(QCGen -> Prop) -> IO Result, need to find property

eca2SQLtest:: eca2PrettySQL -> Doc
eca2SQLtest fs eca = eca2PrettySQL fs eca == pretty (nm, eca2SQL fs eca)

testshowTableSpec :: MkTableSpec (GetRef name) -> String
testshowtableSpec (label::SQLAble) n = SQLAble (fenceName n) == SQLable (Name ("fence"++show n))
