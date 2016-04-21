{-# LANGUAGE ImpredicativeTypes,  TupleSections, UndecidableInstances, TemplateHaskell, ViewPatterns, StandaloneDeriving #-}

module Database.Design.Ampersand.ECA2SQL.Interpreter  
  ( module Database.Design.Ampersand.ECA2SQL.Interpreter 
  ) where 

import Control.Applicative
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Language.SQL.SimpleSQL.Syntax (ValueExpr(..), QueryExpr(..), TableRef(..), Name(..))  
import Data.Proxy (Proxy(..), KProxy(..))
import qualified GHC.TypeLits as TL 
import GHC.TypeLits (Symbol)
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import Data.Function (fix) 
import Database.Design.Ampersand.ECA2SQL.Utils 
import Database.Design.Ampersand.Basics.Assertion
import Database.Design.Ampersand.ECA2SQL.Singletons
import Database.Design.Ampersand.ECA2SQL.TypedSQL
import Database.Design.Ampersand.ECA2SQL.FreshName 
import Text.Read (readMaybe) 

import qualified Data.Map as M 

import Control.Lens 
import Control.Lens.TH 

import Control.Monad.State 
import Control.Monad.Except  

-- import qualified Data.Set as S 

{-
-- TODO: is this useful? 
data CmpKey (f :: k -> *) where 
  CmpKey :: SingT x -> f x -> CmpKey f 

instance (SingKind kp, kp ~ ('KProxy :: KProxy k)) => Eq (CmpKey (f :: k -> *)) where 
  CmpKey a _ == CmpKey b _ = dec2bool $ a %== b 

instance (Ord (ValOfSing kp), SingKind kp, kp ~ ('KProxy :: KProxy k)) => Ord (CmpKey (f :: k -> *)) where 
  CmpKey a _ `compare` CmpKey b _ = cmpSing a b 

newtype TMap (f :: k -> *) = TMap (S.Set (CmpKey f))

lookupTMap :: forall x f kp . (Ord (ValOfSing kp), SingKind kp, kp ~ ('KProxy :: KProxy k), Sing x) => TMap (f :: k -> *) -> Maybe (f x) 
lookupTMap (TMap m) = 
  let inT = sing 
      inT :: SingT x 
  in 
  case S.maxView $ S.difference m (S.difference m (S.singleton (CmpKey inT undefined))) of 
    Nothing -> Nothing 
    Just (CmpKey r v, m') 
      | null m' -> case inT %== r of 
                     Yes Refl -> Just v 
                     _ -> error "lookupTMap" 
      | otherwise -> error "lookupTMap" 

lookupTMap' :: forall f kp . (Ord (ValOfSing kp), SingKind kp, kp ~ ('KProxy :: KProxy k)) => TMap (f :: k -> *) -> Exists (SingT :: k -> *) -> Maybe (Exists f) 
lookupTMap' m (Ex x) = Ex <$> withSingT x (\(Proxy :: Proxy z) -> lookupTMap m :: Maybe (f z))

insertTMap :: (Sing x, Ord (ValOfSing kp), SingKind kp, kp ~ ('KProxy :: KProxy k)) => TMap (f :: k -> *) -> f x -> TMap f 
insertTMap (TMap m) x = TMap $ S.insert (CmpKey sing x) m 
-}

--- Interpreter state 

deriving instance Ord Name 

deriving instance (Show a) => Show (Id a) 

newtype SQLiCell = SQLiCell (Sum Id '[ Integer, Double, String, Bool, () ])
  deriving (Eq, Ord, Show) 

pattern SomeCell x <- SQLiCell (SumElem (unId -> x)) 
  where SomeCell x = SQLiCell (SumElem (Id x))

data Population_ i 
  = Tablei { _tablePop :: M.Map (Nm i) [SQLiCell] } 
  | Vectori { _vectorPop :: [[SQLiCell]] } deriving (Show, Eq) 

data NameK = QNm | UnQNm 

data Nm (x :: NameK) where 
  (:.) :: Name -> Name -> Nm 'QNm 
  UnQualName :: Name -> Nm x 
  
deriving instance Show (Nm x)
deriving instance Eq (Nm x) 
deriving instance Ord (Nm x) 

type Population = forall i . Population_ i 
type QPopulation = Population_ 'QNm

popVal :: Prism' (Population_ i) SQLiCell
popVal = prism (Vectori . pure . pure) (\q -> maybe (Left q) Right $ 
  case q of                                         
    Vectori [[x]] -> Just x 
    Tablei m -> do  
      ([a],m') <- M.maxView m 
      guard (M.null m') >> return a 
    _ -> Nothing)

makePrisms ''Population_ 

data SQLiSt = SQLiSt 
  { _stPopulations :: forall i . M.Map Name (Population_ i)    -- Tables to populations 
  , _stLocalNames  :: forall i . M.Map Name (Population_ i)    -- Locally bounds names 
  , _stReferences  :: M.Map Name SQLiCell                      -- Local and global references 
  }

makeLenses ''SQLiSt

data SQLiErr 
  = UnboundName String Name
  | InvalidLiteral ValueExpr 
  | InvalidExpression String (Either ValueExpr QueryExpr) 

mayToErr :: MonadError e m => e -> Maybe a -> m a
mayToErr e = maybe (throwError e) return  

evalValueExpr :: (MonadError SQLiErr m, MonadState SQLiSt m, MonadFresh '[Name] m) => ValueExpr -> m QPopulation
evalValueExpr Star = 
  Tablei <$> (foldM (\ms (n,pop) -> 
                       case pop of 
                         Vectori ps ->  
                           M.fromList <$> mapM (\p -> (,p) . (n :.) <$> (makeFresh (Name Nothing "col"))) ps 
                         Tablei ps -> return $ M.mapKeysMonotonic (\(UnQualName q) -> n :. q) ps 
                    ) M.empty . M.toList 
             =<< use stLocalNames)

evalValueExpr v@(NumLit rawLit) = 
  (^. re popVal) <$> mayToErr (InvalidLiteral v) ( 
     (SomeCell <$> (readMaybe rawLit :: Maybe Integer)) <|> 
     (SomeCell <$> (readMaybe rawLit :: Maybe Double))
     )

evalValueExpr (StringLit _ str _) = return $ SomeCell str ^. re popVal

evalValueExpr Parameter = 
  throwError $ InvalidExpression 
    "Prepared statement cannot be evaluated\
    \(instantiate the parameters first)" 
    (Left Parameter)

-- evalValueExpr (TypedLit _ str) = return [[ SomeCell str ]] 

-- evalValueExpr (Iden nm) = do 
--   nms <- liftA2 M.union (use stLocalNames) (M.map (pure.pure) <$> use stReferences)
--   mayToErr (UnboundName "iden" nm) (nms ^. at nm)

-- evalQueryExpr :: (MonadError SQLiErr m, MonadState SQLiSt m) => QueryExpr -> m Population 
-- evalQueryExpr (Table nm) = use stPopulations >>= mayToErr (UnboundName "table" nm) . (^. at nm) 
