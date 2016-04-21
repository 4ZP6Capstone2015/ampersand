{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE ViewPatterns , ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
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
import Data.Function (fix) 
import Database.Design.Ampersand.ECA2SQL.Utils 
import Database.Design.Ampersand.Basics.Assertion
import Database.Design.Ampersand.ECA2SQL.Singletons

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

-- Singleton for SQLType 
type SQLTypeS = (SingT :: SQLType -> *) 

type family TyRepOfSQL (x :: SQLType) :: TyRep where 
  TyRepOfSQL 'SQLAtom = 'TyCtr "SQLType_SQLAtom" '[] 
  TyRepOfSQL 'SQLBool = 'TyCtr "SQLType_SQLBool" '[] 
  TyRepOfSQL ('SQLRel x) = 'TyCtr "SQLType_SQLRel" '[TyRepOfSQL x] 
  TyRepOfSQL ('SQLRow x) = 'TyCtr "SQLType_SQLRow" '[TyRepOf x] 
  TyRepOfSQL ('SQLVec x) = 'TyCtr "SQLType_SQLVec" '[TyRepOf x] 

type instance TyRepOf (x :: SQLType) = TyRepOfSQL x 

instance (WitnessSingI xs, NonEmpty xs, IsSetRec xs) => WitnessSingI ('SQLRow xs) where witnessSing = WSQLRow witnessSing 
instance (WitnessSingI xs) => WitnessSingI ('SQLVec xs) where witnessSing = WSQLVec witnessSing
instance (WitnessSingI x) => WitnessSingI ('SQLRel x) where witnessSing = WSQLRel witnessSing 
instance WitnessSingI 'SQLAtom where witnessSing = WSQLAtom 
instance WitnessSingI 'SQLBool where witnessSing = WSQLBool 

instance SingKind ('KProxy :: KProxy SQLType) where 
  withSingW WSQLAtom k = k Proxy 
  withSingW WSQLBool k = k Proxy 
  withSingW (WSQLRel x) k = withSingW x $ const $ k Proxy 
  withSingW (WSQLRow x) k = withSingW x $ const $ k Proxy 
  withSingW (WSQLVec x) k = withSingW x $ const $ k Proxy 

  witness = error "SingKind{SQLType}: TODO - witness" 
  sing2val' = error "SingKind{SQLType}: TODO - sing2val" 
  val2sing' = error "SingKind{SQLType}: TODO - val2sing" 

  data SingWitness ('KProxy :: KProxy SQLType) x args where
    WSQLAtom :: SingWitness 'KProxy 'SQLAtom    ( 'TyCtr "SQLType_SQLAtom" '[] )
    WSQLBool :: SingWitness 'KProxy 'SQLBool    ( 'TyCtr "SQLType_SQLBool" '[] )
    WSQLRel  :: !(SingWitness 'KProxy x xr)
             -> SingWitness 'KProxy ('SQLRel x) ( 'TyCtr "SQLType_SQLRel" '[xr] )
    WSQLRow  :: (NonEmpty x, IsSetRec x) => !(SingWitness 'KProxy x xr)
             -> SingWitness 'KProxy ('SQLRow x) ( 'TyCtr "SQLType_SQLRow" '[xr] )
    WSQLVec  :: !(SingWitness 'KProxy x xr)
             -> SingWitness 'KProxy ('SQLVec x) ( 'TyCtr "SQLType_SQLVec" '[xr] )

  type ValOfSing ('KProxy :: KProxy SQLType) = SQLType


-- Determine if a SQL type is a really a scalar type. 
type family IsScalarType (x :: k) :: Bool where 
  IsScalarType ('SQLRel x) = 'False 
  IsScalarType ('SQLRow x) = 'False
  IsScalarType ('SQLVec x) = 'False
  IsScalarType 'SQLBool = 'True
  IsScalarType 'SQLAtom = 'True

type family IsScalarTypes (x :: [SQLType]) :: Bool where 
  IsScalarTypes '[] = 'True 
  IsScalarTypes (x ': xs) = IsScalarType x && IsScalarTypes xs 
  
isScalarType :: SingT (x :: SQLType) -> SingT (IsScalarType x)
isScalarType (SingT x) = 
  case x of
    WSQLAtom -> STrue 
    WSQLBool -> STrue 
    (WSQLVec _vs0) -> SFalse 
    (WSQLRow _ts0) -> SFalse 
    (WSQLRel _) -> SFalse   

isScalarTypes :: SingT xs -> SingT (IsScalarTypes xs) 
isScalarTypes s = elimSingT s $ \case 
  WNil -> STrue 
  WCons x xs -> isScalarType (SingT x) |&& isScalarTypes (SingT xs)

-- A SQL value contains value expressions. Using the constructors directly is unsafe. 
-- The type of underlying prim expr is dependant on whether it is a scalar type or not. 
data SQLVal (a :: SQLType) where 
  SQLScalarVal :: (IsScalarType a ~ 'True, Sing a) => ValueExpr -> SQLVal a 
  SQLQueryVal :: (IsScalarType a ~ 'False, Sing a) => QueryExpr -> SQLVal a 

-- Get the type of a value 
typeOf :: SQLVal a -> SingT a 
typeOf SQLScalarVal{} = sing 
typeOf SQLQueryVal{} = sing 

-- Get the argument of a relation
argOfRel :: forall x . SingT ('SQLRel x) -> SingT x
argOfRel (SingT (WSQLRel x)) = SingT x 

-- Semantics in the interpreter. Underscores mark unsafe ctrs. 
data SQLValSem (x :: SQLRefType) where 
  Unit :: SQLValSem 'SQLUnit
  Method_ :: (Sing args, Sing out) => Name -> SQLValSem ('SQLMethod args out) 
  Ref_ :: Sing x => Name -> SQLValSem ('SQLRef x) 
  Val :: { valOfValSem :: SQLVal x } -> SQLValSem ('Ty x) 

-- Pattern match only (no constructor syntax). These permit access (but not the
-- ability to construct) to the underlying untyped representation. 
pattern Method nm <- Method_ nm 
pattern GetRef x <- Ref_ x 

-- Get the sql type of a semantic value which represens a value or reference
-- to an actual type. 
typeOfSem :: (f `IsElem` '[ 'SQLRef, 'Ty ]) => SQLValSem (f x) -> SQLTypeS x 
typeOfSem Ref_{} = sing 
typeOfSem (Val x) = typeOf x 
typeOfSem x = impossible  "A SQLVal{Ref/Ty} was not a {Ref/Val}" (WHNFIsNF x) 

-- Get the columns of a sql row.   
colsOf :: SingT ('SQLRow xs) -> SingT xs
colsOf (SingT (WSQLRow r)) = SingT r 

-- A SQLValRef is a reference to a sql value in the domain of the semantic interpretation. 
type SQLValRef x = SQLValSem ('SQLRef x)

-- Same as above, but a reference to a method is distinct from that to a value. 
type SQLMethodRef args out = SQLValSem ('SQLMethod args out) 

unsafeSqlValFromName :: forall x . Sing x => Name -> SQLVal x 
unsafeSqlValFromName nm = 
  elimSingT (isScalarType (sing :: SingT x)) $ \case 
    WTrue -> SQLScalarVal $ Iden [nm] 
    WFalse -> SQLQueryVal $ Table [nm] 

-- Unsafely generate a SQL value representing a query statement
-- from an untype QueryExpr. 
unsafeSQLValFromQuery :: forall xs . (NonEmpty xs, Sing ('SQLRel ('SQLRow xs))) => QueryExpr -> SQLVal ('SQLRel ('SQLRow xs))
unsafeSQLValFromQuery = SQLQueryVal

unsafeRefFromName :: SingT x -> Name -> SQLValRef x
unsafeRefFromName ty nm = withSingT ty $ \_ -> Ref_ nm

deref :: forall x . SQLValRef x -> SQLVal x 
deref (Ref_ nm) = unsafeSqlValFromName nm 

-- SQL statements

-- The specification of a table is a reference to a relation on rows 
-- of the table type. 
data TableSpec t where 
  MkTableSpec :: { getTableSpec :: !(SQLValRef ('SQLRel ('SQLRow t))) } -> TableSpec t
  TableAlias_  :: !(SingT newNames) -> !(TableSpec t0) -> TableSpec (ZipRec newNames (RecAssocs t0)) 

-- Get the type of a table spec. This returns a `SQLRow t' instead of just a `t'
-- simply because the proof of (UniqueLabels && NonEmpty) is packaged in with `SQLRow t'
-- but not `t'
typeOfTableSpec :: forall t . TableSpec t -> SingT ('SQLRow t) 
typeOfTableSpec t = t `seq` 
  let q :: forall q . TableSpec q -> Dict (NonEmpty q &*& IsSetRec q)
      q t' = 
        case t' of 
          (MkTableSpec (typeOfSem -> SingT (WSQLRel (WSQLRow _)))) -> Dict 
          (TableAlias_ _ _) -> error "TODO" -- q t' 

  in case typeOfTableSpec' t of { SingT x -> case q t of { Dict -> SingT (WSQLRow x) } }

typeOfTableSpec' :: TableSpec t -> SingT t
typeOfTableSpec' (MkTableSpec x) = 
  case typeOfSem x of 
    SingT (WSQLRel (WSQLRow t)) -> SingT t
    q -> impossible "Type of a table not (Rel (Row x)) f.s. x" q

typeOfTableSpec' (TableAlias_ nms t') = tr nms $ recAssocs $ typeOfTableSpec' t' where 
  tr :: SingT newNames -> SingT xs -> SingT (ZipRec newNames xs) 
  tr (SingT WNil) (SingT WNil) = SingT WNil 
  tr (SingT (WCons x xs)) (SingT (WCons y ys)) = 
    case tr (SingT xs) (SingT ys) of { SingT rs -> SingT (WCons (WRecLabel x y) rs) }
  tr (SingT WCons{}) (SingT WNil) = impossible  "ZipRec exists but is not defined" () 
  tr (SingT WNil{}) (SingT WCons{}) = impossible  "ZipRec exists but is not defined" () 

-- Safely create a table spec. 
tableSpec :: (IsSetRec x, NonEmpty x) => Name -> SingT x -> TableSpec x 
tableSpec tn xs@(SingT x) = 
  case x of 
    WNil -> impossible  "NonEmpty exists but given type is the empty list" () 
    WCons{} -> MkTableSpec $ withSingT xs $ \_ -> Ref_ tn 

-- Can return nothing if the set of names is not valid 
tableSpec' :: Name -> Prod (K String :*: SingT) tys -> (forall ks . Maybe (RecAssocs ks :~: tys, TableSpec ks) -> r) -> r
tableSpec' nm0 tys0 k0 = 
    tr tys0 $ \case 
      Nothing -> k0 Nothing 
      Just (pr,ty@(SingT ty')) -> 
        case (decSetRec ty, ty') of 
          (Yes p, WCons{}) -> openSetRec p $ k0 $ Just (pr, tableSpec nm0 (SingT ty'))
          (Yes{}, WNil{}) -> k0 Nothing
          (No{},_) -> k0 Nothing
  where 
    tr :: Prod (K String :*: SingT) tys -> (forall (ks :: [RecLabel Symbol SQLType]) 
            . Maybe (RecAssocs ks :~: tys, SingT ks) -> r) -> r
    tr PNil k = k Nothing 
    tr (PCons (K nm :*: SingT x) PNil) k = 
        case TL.someSymbolVal nm of 
          TL.SomeSymbol nmTy -> k (Just (Refl, SingT (WCons (WRecLabel (WSymbol nmTy) x) WNil ) )) 
    tr (PCons (K nm :*: (SingT x :: SingT x0)) xs@PCons{}) k = 
      tr xs $ \case 
         Nothing -> k Nothing 
         Just (Refl, SingT rs) -> 
           case TL.someSymbolVal nm of 
             TL.SomeSymbol nmTy -> k (Just (Refl, SingT (WCons (WRecLabel (WSymbol nmTy) x) rs ) )) 

-- Create an table spec from runtime information. Returns Nothing if the table
-- would not be valid. 
someTableSpec :: Name -> [(String, Exists SQLTypeS)] -> Maybe (Exists TableSpec) 
someTableSpec tn cols = 
  mkSingNames cols #>> \colSing@(SingT cols') -> 
  case decSetRec colSing of 
    Yes q -> 
      case cols' of 
        WNil{} -> Nothing
        WCons{} -> openSetRec q $ Just $ Ex $ tableSpec tn colSing 
    No{}  -> Nothing 

  where 
    mkSingNames :: [(String, Exists SQLTypeS)] -> Exists (SingT :: [RecLabel Symbol SQLType] -> *) 
    mkSingNames [] = Ex $ SingT WNil 
    mkSingNames ((nm, Ex (SingT ty)):r) = 
      case TL.someSymbolVal nm of 
        TL.SomeSymbol nmTy -> mkSingNames r #>> \(SingT q) -> Ex $ SingT (WCons (WRecLabel (WSymbol nmTy) ty) q)


-- A SQL method 
data SQLMethod ts out where 
  MkSQLMethod :: {-(IsScalarTypes ts ~ 'True, IsScalarType out ~ 'True) -} () 
              => SingT ts -> (Prod (SQLValSem :.: 'SQLRef) ts -> SQLSt 'Mthd ('Ty out)) -> SQLMethod ts out 
  -- A method with a set of input parameters. The function takes a vector of
  -- references of those types.

  SQLMethodWithFormalParams :: {-(IsScalarTypes ts ~ 'True, IsScalarType out ~ 'True) -} () 
                            => Prod (SQLValSem :.: 'SQLRef) ts -> SQLSt 'Mthd ('Ty out) -> SQLMethod ts out 
  -- A method with formal parameters - using this is considered unsafe. 

-- Used to distinguish sql methods from statements. The only difference is that
-- a method cannot be "sequenced" with `:>>='. Essentially this allows us to
-- define the SQLRet constructor (see below) in a way such that the type system
-- enforces that that branch always returns. 
data SQLSem = Stmt | Mthd 

type SQLStatement = SQLSt 'Stmt

data SQLSt (x :: SQLSem) (a :: SQLRefType) where
  Insert :: TableSpec ts -> SQLVal ('SQLRel ('SQLRow ts)) -> SQLStatement 'SQLUnit 
  -- Given a table and a query, insert those values into that table. Overloaded to work with both vectors and 
  -- tables. If the input is a table, it is implicitly casted to the shape of the table before insertion. 

  Delete :: TableSpec ts -> (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> SQLStatement 'SQLUnit 
  -- Delete from a table those values specified by the predicate
 
  Update :: TableSpec ts -> (SQLVal ('SQLRow ts) -> SQLVal 'SQLBool) -> (SQLVal ('SQLRow ts) -> SQLVal ('SQLRow ts)) -> SQLStatement 'SQLUnit 
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

  IfSQL :: SQLVal 'SQLBool -> SQLSt t0 a -> SQLSt t1 b -> SQLStatement 'SQLUnit
  -- An If statement takes a boolean valued expression. 
 
  (:>>=) :: SQLStatement a -> (SQLValSem a -> SQLSt x b) -> SQLSt x b 
  SQLNoop :: SQLStatement 'SQLUnit 
  SQLRet :: SQLVal a -> SQLSt 'Mthd ('Ty a)
  -- Semantics. Only allowed for sql types. 

  SQLFunCall :: SQLMethodRef ts out -> Prod SQLVal ts -> SQLStatement ('Ty out) 
  SQLDefunMethod :: SQLMethod ts out -> SQLStatement ('SQLMethod ts out)
  -- Methods 

