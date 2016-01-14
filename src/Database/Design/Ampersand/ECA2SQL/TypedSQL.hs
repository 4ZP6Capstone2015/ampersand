{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL.TypedSQL 
  ( module Database.Design.Ampersand.ECA2SQL.TypedSQL 
  , module Sm
{- TODO exports list 
    Prod(..), Sum(..), All(..), Elem(..), AppliedTo(..), DecideEq(..), Sing(..), SingT(..), (:~:)(..), withSingT
  , IfA(..), if_ap, if_pure
  -- SQL stuff
  , Symbol, SymbolSing, Nat, NatSing, RecLabel(..), SQLType(..), SQLRefType, SQLRow, SQLVec, SQLRel, SQLAtom, SQLBool
  , SQLTypeS, SQLValProto, bimapProto, foldProto, SQLVal, SQLValSem(Unit) -- Ctrs not exported!
  , pattern Method, pattern Ref, pattern Val
  , unsafeSqlValFromName, deref
  , TableSpec, SQLMethod(..), SQLSem, SQLStatement, IsScalarType, isScalarType
  , SQLSt(..)
  , getSQLVal, elimSQLVal, unsafeSQLVal, typeOf 
-} 
  ) where 

import Control.Applicative
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Language.SQL.SimpleSQL.Syntax (ValueExpr(..), QueryExpr(..), TableRef(..), Name(..))  
import Data.Proxy (Proxy(..), KProxy(..))
import qualified GHC.TypeLits as TL 
import GHC.TypeLits (Symbol)
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce 
import Database.Design.Ampersand.ECA2SQL.Utils 

-- Basic model SQL types represented in Haskell 

-- SQL Types 
data SQLType 
  = SQLAtom                            -- All scalar types. Should be split into the different types it represents 
  | SQLBool                            -- A boolean
  | SQLRel SQLType                     -- Type of relations over some underlying type
  | SQLRow [RecLabel Symbol SQLType]   -- A row in a table. 
  | SQLVec [SQLType]                   -- Essentially an unnamed row. 

-- SQL types along with types in domain of interpretation 
data SQLRefType 
  = Ty SQLType 
  | SQLRef SQLType 
  | SQLUnit 
  | SQLMethod [SQLType] SQLType 

-- Useful type synonyms 
type SQLRow xs = 'Ty ('SQLRow xs) 
type SQLVec xs = 'Ty ('SQLVec xs) 
type SQLRel x = 'Ty ('SQLRel x) 
type SQLAtom = 'Ty 'SQLAtom 
type SQLBool = 'Ty 'SQLBool 

-- Singletong for SQL values. It is the same as SQL values by construction. 
type SQLTypeS = (SingT :: SQLType -> *) 
data instance SingT (x :: SQLType) where 
  SSQLAtom :: SingT 'SQLAtom 
  SSQLBool :: SingT 'SQLBool
  SSQLRow :: NonEmpty ts => Prod SingT ts -> SingT ('SQLRow ts)
  SSQLVec :: Prod SingT ts -> SingT ('SQLVec ts) 
  SSQLRel :: SingT x -> SingT ('SQLRel x) 

-- Determine if a SQL type is a really a scalar type. 
type family IsScalarType (x :: k) :: Bool where 
  IsScalarType ('SQLRel x) = 'False 
  IsScalarType ('SQLRow x) = 'False
  IsScalarType ('SQLVec x) = 'False
  IsScalarType 'SQLBool = 'True
  IsScalarType 'SQLAtom = 'True
  
  -- IsScalarType ('SQLRow x) = IsScalarType x 
  -- IsScalarType ('SQLVec x) = IsScalarType x 
  -- IsScalarType ((nm :: Symbol) ::: (x :: SQLType)) = IsScalarType x 
  -- IsScalarType '[] = 'True 
  -- IsScalarType (x ': xs) = IsScalarType x && IsScalarType xs 

isScalarType :: SingT (x :: SQLType) -> SingT (IsScalarType x)
isScalarType SSQLAtom = STrue 
isScalarType SSQLBool = STrue 
isScalarType (SSQLVec vs0) = SFalse {-
  case vs0 of 
    PNil -> STrue
    PCons v vs ->  isScalarType v |&& isScalarType (SSQLVec vs) -} 
isScalarType ((SSQLRow ts0)) = SFalse {-
  case ts0 of 
    PCons (SRecLabel _ t) PNil       -> 
      case isScalarType t of 
        STrue -> STrue 
        SFalse -> SFalse 
    PCons (SRecLabel _ t) ts@PCons{} -> isScalarType t |&& isScalarType (SSQLRow  ts)
    _ -> error "impossible" -}
isScalarType (SSQLRel _) = SFalse   

-- Singletons for SQLType 
instance (All Sing xs, NonEmpty xs) => Sing ('SQLRow xs) where sing = SSQLRow (mkProdC (Proxy :: Proxy Sing) sing) 
instance (All Sing xs) => Sing ('SQLVec xs) where sing = SSQLVec (mkProdC (Proxy :: Proxy Sing) sing) 
instance Sing 'SQLAtom where sing = SSQLAtom 
instance Sing 'SQLBool where sing = SSQLBool 

-- A SQL value contains value expressions. Using the constructors directly is unsafe. 
data SQLVal (a :: SQLType) where 
  SQLScalarVal :: (IsScalarType a ~ 'True, Sing a) => ValueExpr -> SQLVal a 
  SQLQueryVal :: (IsScalarType a ~ 'False, Sing a) => QueryExpr -> SQLVal a 

-- Get the type of a value 
typeOf :: SQLVal a -> SingT a 
typeOf SQLScalarVal{} = sing 
typeOf SQLQueryVal{} = sing 

-- Semantics in the interpreter 
data SQLValSem (x :: SQLRefType) where 
  Unit :: SQLValSem 'SQLUnit
  Method_ :: (Sing args, Sing out) => Name -> SQLValSem ('SQLMethod args out) 
  Ref_ :: Sing x => Name -> SQLValSem ('SQLRef x) 
  Val_ :: SQLVal x -> SQLValSem ('Ty x) 
  
-- A SQLValRef is a reference to a sql value in the domain of the semantic interpretation. 
type SQLValRef x = SQLValSem ('SQLRef x)

-- Same as above, but a reference to a method is distinct from that to a value. 
type SQLMethodRef args out = SQLValSem ('SQLMethod args out) 

unsafeSqlValFromName :: forall x . Sing x => Name -> SQLVal x 
unsafeSqlValFromName nm = case isScalarType (sing :: SingT x) of 
                            STrue -> SQLScalarVal $ Iden [nm] 
                            SFalse -> SQLQueryVal $ Table [nm] 

deref :: forall x . SQLValRef x -> SQLVal x 
deref (Ref_ nm) = unsafeSqlValFromName nm 

-- Pattern match only (no constructor syntax). These permit access (but not the
-- ability to construct) to the underlying untyped representation. 
-- pattern Method nm <- Method_ nm 
-- pattern Ref x <- Ref_ x 
-- pattern Val x <- Val_ x 

instance DecideEq (SingT :: SQLType -> *) where 
  SSQLAtom %==  (SSQLAtom ) = Just Refl 
  SSQLBool %==  (SSQLBool ) = Just Refl 
  SSQLRel  x %==  (SSQLRel  y) = fmap (cong Refl) (x %== y)
  SSQLRow  ts0 %==  (SSQLRow  ts1) = fmap (cong Refl) (ts0 %== ts1)
  SSQLVec  ts0 %==  (SSQLVec  ts1) = fmap (cong Refl) (ts0 %== ts1)
  _ %== _ = Nothing 

instance (DecideEq (SingT :: k0 -> *), DecideEq (SingT :: k1 -> *)) => DecideEq (SingT :: RecLabel k0 k1 -> *) where 
  SRecLabel a0 b0 %== SRecLabel a1 b1 = liftA2 (cong2 Refl) (a0 %== a1) (b0 %== b1) 

-- SQL statements

-- The specification of a table is a reference to a relation on rows 
-- of the table type. 
type TableSpec t = SQLValRef ('SQLRel ('SQLRow t))

-- A method with a set of input parameters. The function takes a vector of references
-- of those types.
data SQLMethod ts out where 
  MkSQLMethod :: Maybe String -> (Prod SQLVal ts -> SQLSt 'Mthd ('Ty out)) -> SQLMethod ts out 

-- Used to distinguish sql methods from statements. The only difference 
-- is that a method cannot be "sequenced" with `:>>='. Essentially this
-- allows us to define 
data SQLSem = Stmt | Mthd 

type SQLStatement = SQLSt 'Stmt

data SQLSt (x :: SQLSem) (a :: SQLRefType) where
  Insert :: TableSpec ts -> SQLVal ('SQLRel ('SQLRow ts)) -> SQLStatement 'SQLUnit 
  -- Given a table and a query, insert those values into that table. Overloaded to work with both vectors and 
  -- tables. If the input is a table, it is implicitly casted to the shape of the table before insertion. 

  Delete :: TableSpec ts -> SQLVal 'SQLBool -> SQLStatement 'SQLUnit 
  -- Delete from a table those values specified by the predicate
 
  Update :: TableSpec ts -> SQLVal 'SQLBool -> (SQLValRef ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> SQLStatement 'SQLUnit 
  -- Same as above, this time taking two functions, the first is again the where
  -- clause, the 2nd computes the values to be updated. 

  SetRef :: SQLValRef x -> SQLVal x -> SQLStatement 'SQLUnit 
  -- Set the value of a reference to the given value. 

  NewRef :: (IsScalarType a ~ 'True) => SQLTypeS a -> Maybe String -> Maybe (SQLVal a) -> SQLStatement ('SQLRef a) 
  -- Creates a new reference of the given type. Optionally takes a name to use
  -- as a prototype for the new name, and an initial value. The default initial
  -- value of the reference is null. We only allow references to scalar types -
  -- otherwise, a table should be used.

  MakeTable :: SQLTypeS ('SQLRow t) -> SQLStatement ('SQLRef ('SQLRel ('SQLRow t)))
  -- Returns a reference to a new table created with the given signature.  

  DropTable :: TableSpec t -> SQLStatement 'SQLUnit 
  -- Create/dropping tables. Should really bind some sort of table reference, 
  -- but this prevents referencing tables which are known to exist, but
  -- are never bound in the tree. Perhaps there should be some sort of 
  -- "assumptions" constructor for tables?

  IfSQL :: SQLVal 'SQLBool -> SQLSt t0 a -> SQLSt t1 a -> SQLStatement a   
  -- An If statement takes a boolean valued expression. 
 
  (:>>=) :: SQLStatement a -> (SQLValSem a -> SQLSt x b) -> SQLSt x b 
  SQLNoop :: SQLStatement 'SQLUnit 
  SQLRet :: SQLVal a -> SQLSt 'Mthd ('Ty a)
  -- Semantics. Only allowed for sql types. 

  SQLFunCall :: SQLMethodRef ts out -> Prod SQLVal ts -> SQLStatement ('Ty out) 
  SQLDefunMethod :: SQLMethod ts out -> SQLStatement ('SQLMethod ts out)
  -- Methods 

