{-# LANGUAGE ScopedTypeVariables, ImpredicativeTypes,  TupleSections, UndecidableInstances, TemplateHaskell, ViewPatterns, StandaloneDeriving #-}

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

import qualified Data.Coerce as C 

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

cell2ValueExpr :: SQLiCell -> ValueExpr
cell2ValueExpr = \case 
  SomeCell (i :: Integer) -> NumLit $ show i 
  SomeCell (i :: Double)  -> NumLit $ show i 
  SomeCell i -> StringLit "" i "" 
  SomeCell () -> Iden [ Name Nothing "NULL" ] 
  SomeCell b -> Iden [ Name Nothing (if b then "TRUE" else "FALSE") ] 
  _ -> impossible (Justification ["Unexpected impossible case"]) () 

data NameK = QNm | UnQNm 

data Nm (x :: NameK) where 
  (:.) :: Name -> Name -> Nm 'QNm 
  UnQualName :: Name -> Nm x 

data Population_ i 
  = Tablei { _tablePop :: M.Map (Nm i) [SQLiCell] } 
  | Vectori { _vectorPop :: [[SQLiCell]] } deriving (Show, Eq) 
makePrisms ''Population_ 

deriving instance Show (Nm x)
deriving instance Eq (Nm x) 
deriving instance Ord (Nm x) 

type QPopulation = Population_ 'QNm

popVal :: Prism' (Population_ i) SQLiCell
popVal = prism (Vectori . pure . pure) (\q -> maybe (Left q) Right $ 
  case q of                                         
    Vectori [[x]] -> Just x 
    Tablei m -> do  
      ([a],m') <- M.maxView m 
      guard (M.null m') >> return a 
    _ -> Nothing)

popCol :: Prism' (Population_ i) [SQLiCell]
popCol = prism' (Vectori . pure) $ \case 
           Vectori [x] -> Just x 
           Tablei m -> M.maxView m >>= \(a,m') -> guard (M.null m') >> return a 
           _ -> Nothing 

popCols :: Iso' [[SQLiCell]] (Population_ i) -- 
popCols = iso Vectori $ \case 
            Vectori x -> x 
            Tablei m -> M.elems m 


data SQLiSt = SQLiSt 
  { _stPopulations :: forall i . M.Map Name (Population_ i)    -- Tables to populations 
  , _stLocalNames  :: forall i . M.Map Name (Population_ i)    -- Locally bounds names 
  , _stReferences  :: M.Map Name SQLiCell                      -- Local and global references 
  }

makeLenses ''SQLiSt

-----------------


data SQLiErr 
  = UnboundName Name
  | InvalidLiteral ValueExpr 
  | InvalidExpression String (Either ValueExpr QueryExpr) 

unsupported :: MonadError SQLiErr m => ValueExpr -> m a
unsupported x = throwError $ InvalidExpression "Unsupported expression" (Left x) 

mayToErr :: MonadError e m => e -> Maybe a -> m a
mayToErr e = maybe (throwError e) return  

nmsToQNm :: MonadError SQLiErr m => [Name] -> m (Exists Nm) 
nmsToQNm e = 
  case e of 
    [x] -> return $ Ex $ UnQualName x 
    [x,y] -> return $ Ex $ x :. y 
    _ -> throwError $ InvalidExpression "Identifier with more than one compound name" (Left $ Iden e)

evalNm :: (MonadState SQLiSt m, MonadError SQLiErr m) => Nm x -> m QPopulation 
evalNm (UnQualName nm) = do 
  tbls <- mapM use [stPopulations, stLocalNames]
  refs <- M.map (review popVal) <$> use stReferences
  mayToErr (UnboundName nm) $ M.lookup nm (M.unions $ refs : tbls) 
evalNm (ql :. nm) = 
  evalNm (UnQualName ql) >>= \case 
    Vectori{} -> throwError $ InvalidExpression 
                    "Compound name refers \
                    \to a value without columns" 
                    (Left $ Iden [ql, nm])    
    Tablei m -> (review popCol) <$> mayToErr (UnboundName nm) (M.lookup (UnQualName nm) m)

type BinOp a = a -> a -> a 
type BinOpM m a = a -> a -> m a 
type UnOp a = a -> a 
type UnOpM m a = a -> m a

evalFun :: MonadError SQLiErr m => [Name] -> m ([QPopulation] -> m QPopulation) 
evalFun = undefined 

evalUnOp :: MonadError SQLiErr m => [Name] -> m (UnOpM m QPopulation) 
evalUnOp nms@[Name Nothing "NOT"] = return $ 
  \x -> case preview popVal x of 
          Just (SomeCell b) -> return $ review popVal $ SomeCell (not b) 
          _ -> throwError $ 
            InvalidExpression "NOT applied to a non-boolean value" 
                              (Left $ PrefixOp nms (SubQueryExpr Sm.SqSq $ Values $ 
                                                    map (map cell2ValueExpr) $ review popCols x
                                                    ) ) 

evalUnOp nms = throwError $ InvalidExpression "Invalid unary operator" $ Left $ Iden nms 

evalBinOp :: MonadError SQLiErr m => [Name] -> m (BinOpM m QPopulation) 
evalBinOp [Name Nothing "IN"] = return $ 
  let in_ xs ys = all (\x -> any (== x) ys) xs
  in \x y -> return $ review popVal $ SomeCell (in_ (review popCols x) (review popCols y))
evalBinOp [a@(Name Nothing "NOT"), b@(Name Nothing "IN")] = do 
  liftA2 (\not_ in_ x y -> not_ =<< in_ x y) (evalUnOp [a]) (evalBinOp [b]) 
evalBinOp nms = throwError $ InvalidExpression "Invalid binary operator" $ Left $ Iden nms 


evalValueExpr :: (MonadError SQLiErr m, MonadState SQLiSt m, MonadFresh '[Name] m) => ValueExpr -> m QPopulation
evalValueExpr Star = 
  Tablei <$> (foldM (\ms (n,pop) -> M.union ms <$> 
                       case pop of 
                         Vectori ps ->  
                           M.fromList <$> mapM (\p -> (,p) . (n :.) <$> (makeFresh (Name Nothing "col"))) ps 
                         Tablei ps -> return $ M.mapKeysMonotonic (\(UnQualName q) -> n :. q) ps 
                    ) M.empty . M.toList 
             =<< use stLocalNames)

evalValueExpr v@(NumLit rawLit) = 
  (review popVal) <$> mayToErr (InvalidLiteral v) ( 
     (SomeCell <$> (readMaybe rawLit :: Maybe Integer)) <|> 
     (SomeCell <$> (readMaybe rawLit :: Maybe Double))
     )

evalValueExpr (StringLit _ str _) = return $ review popVal $ SomeCell str 

evalValueExpr Parameter = 
  throwError $ InvalidExpression 
    "Prepared statement cannot be evaluated\
    \(instantiate the parameters first)" 
    (Left Parameter)

evalValueExpr (Iden xs) = nmsToQNm xs >>= (#>> evalNm) 

evalValueExpr (BinOp e0 binOp e1) = do 
  v0  <- evalValueExpr e0
  v1  <- evalValueExpr e1
  (~~) <- evalBinOp binOp
  v0 ~~ v1 
evalValueExpr (PrefixOp pOp e0) = evalUnOp pOp >>= \f -> evalValueExpr e0 >>= \x -> f x 
evalValueExpr (PostfixOp pOp e0) = evalValueExpr (PrefixOp pOp e0) 
evalValueExpr (App fun e0) = evalFun fun >>= \f -> mapM evalValueExpr e0 >>= \x -> f x 

evalValueExpr (Cast x _) = evalValueExpr x 
evalValueExpr (Parens x) = evalValueExpr x 

evalValueExpr (Case tst cases elseCase) = undefined 

evalValueExpr x@TypedLit{} = unsupported x
evalValueExpr x@IntervalLit{} = unsupported x
evalValueExpr x@HostParameter{} = unsupported x 
evalValueExpr x@SpecialOp{} = unsupported x 
evalValueExpr x@AggregateApp{} = unsupported x 
evalValueExpr x@AggregateAppGroup{} = unsupported x 
evalValueExpr x@SpecialOpK{} = unsupported x 
evalValueExpr x@WindowApp{} = unsupported x 
evalValueExpr x@QuantifiedComparison{} = unsupported x 

evalQueryExpr :: (MonadError SQLiErr m, MonadState SQLiSt m) => QueryExpr -> m QPopulation 
evalQueryExpr (Table nm) = locally (\SQLiSt{..} -> SQLiSt { _stLocalNames = M.empty 
                                                          , _stReferences = M.empty 
                                                          , .. 
                                                          })
                                   (nmsToQNm nm >>= (#>> evalNm)) 
