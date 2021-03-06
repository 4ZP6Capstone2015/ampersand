{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE ViewPatterns, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators, MagicHash #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

-- Various utilities used by ECA2SQL 

module Database.Design.Ampersand.ECA2SQL.Utils 
  ( module Database.Design.Ampersand.ECA2SQL.Utils 
  , module GHC.TypeLits 
  , module Data.Proxy
  , module GHC.Exts
  , module Data.Type.Equality
  , module Database.Design.Ampersand.ECA2SQL.Equality 
  , module Database.Design.Ampersand.Basics.Assertion
  ) where 

import Control.Applicative 
import Unsafe.Coerce 
import Data.Proxy (Proxy(..), KProxy(..))
import GHC.TypeLits (Symbol, symbolVal, sameSymbol, KnownSymbol)
import qualified GHC.TypeLits as TL  
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (IsString(..), Any)
import qualified GHC.Exts as Exts 
import Language.SQL.SimpleSQL.Syntax (Name(..))
import Database.Design.Ampersand.ECA2SQL.Equality 
import Database.Design.Ampersand.ECA2SQL.Singletons
import Database.Design.Ampersand.Basics.Assertion (Justification(..), impossible) 
import Control.DeepSeq
import Control.Monad.State.Class 

-- A newtype whose NFData instance assume that `nf x == rnf x`
-- for any `x` which is wrapped in the type. 
newtype WHNFIsNF a = WHNFIsNF a 
instance NFData (WHNFIsNF a) where 
  rnf x = x `seq` () 

instance IsString Name where fromString = Name Nothing 

-- Given a functor `f', `Prod f' constructs the n-ary product category of `f'
data Prod (f :: k -> *) (xs :: [k]) where 
  PNil :: Prod f '[] 
  PCons :: f x -> Prod f xs -> Prod f (x ': xs) 

instance (All (NFData &.> f) xs) => NFData (Prod f xs) where 
  rnf = foldrProdC (Proxy :: Proxy (NFData &.> f)) () deepseq

prod2sing :: forall xs . (SingKind ('KProxy :: KProxy k)) => Prod SingT (xs :: [k]) -> SingT (xs :: [k])
prod2sing x0 = SingT (go x0) where 
  go :: forall (xs' :: [k]) . Prod SingT xs' -> SingWitness 'KProxy xs' (TyRepOf xs')
  go PNil = WNil 
  go (PCons (SingT x) xs) = 
    case witness x of 
      (Refl, Dict) -> WCons x (go xs) 

sing2prod :: forall xs . (SingKind ('KProxy :: KProxy k)) => SingT (xs :: [k]) -> Prod SingT (xs :: [k]) 
sing2prod (SingT x0) = go x0 where 
  go :: forall (xs' :: [k]) rep . SingWitness 'KProxy xs' rep -> Prod SingT xs'
  go WNil = PNil 
  go (WCons x xs) = PCons (SingT x) (go xs) 

{-
foldrProd : forall (k : *) (f : k -> *) (xs : [k]) (acc : *) (o : k -> acc -> acc) (g : acc -> *)
          -> Prod f xs 
          -> g [] 
          -> (forall (a : acc) -> pi (x : k) -> g a -> g (o x a)) 
          -> g xs
the real type 
-}

foldrProd :: acc -> (forall q . f q -> acc -> acc) -> Prod f xs -> acc 
foldrProd z _ PNil = z 
foldrProd z f (PCons x xs) = f x (foldrProd z f xs) 

foldrProd' :: (forall x xs . f x -> Prod g xs -> Prod g (x ': xs)) 
            -> Prod f xs1 -> Prod g xs1 
foldrProd' _ PNil = PNil 
foldrProd' f (PCons x xs) = f x (foldrProd' f xs) 

data Holds c x where Holds :: c x => Holds c x 

foldrProdC :: forall c xs acc f . All c xs => Proxy c -> acc -> (forall q . c q => f q -> acc -> acc) -> Prod f xs -> acc 
foldrProdC pr z f = foldrProd z (\((Holds :: Holds c q0) :*: b) -> f b) . (zipProd (:*:) (mkProdC pr Holds))

zipProd :: (forall x . f x -> g x -> h x) -> Prod f xs -> Prod g xs -> Prod h xs 
zipProd _ PNil PNil = PNil 
zipProd q (PCons x xs) (PCons y ys) = PCons (q x y) (zipProd q xs ys)
zipProd _ q0 q1 = impossible "zipProd" (WHNFIsNF (q0, q1)) 

foldlProd :: acc -> (forall q . f q -> acc -> acc) -> Prod f xs -> acc 
foldlProd z _ PNil = z 
foldlProd z f (PCons x xs) = foldlProd (f x z) f xs 
  
mapProd :: (forall x . f x -> g x) -> Prod f xs -> Prod g xs
mapProd _ PNil = PNil 
mapProd f (PCons x xs) = PCons (f x) (mapProd f xs)

infixr 5 :> 
pattern x :> xs = PCons x xs 

someProd :: [Exists f] -> Exists (Prod f)
someProd [] = Ex PNil 
someProd (Ex x:xs) = someProd xs #>> Ex . PCons x

data Sum (f :: k -> *) (xs :: [k]) where 
  SHere :: f x -> Sum f (x ': xs) 
  SThere :: Sum f xs -> Sum f (x ': xs) 

instance All (Ord &.> f) zs => Eq (Sum f zs) where 
  (==) a b = compare a b == EQ 

instance All (Ord &.> f) zs => Ord (Sum f zs) where 
  compare = eqSum (mkProdC (Proxy :: Proxy (Ord &.> f)) Holds) where 
    eqSum :: Prod (Holds (Ord &.> f)) xs -> Sum f xs -> Sum f xs -> Ordering 
    eqSum PNil x _y = case x of 
    eqSum (PCons Holds _) (SHere f) (SHere g) = f `compare` g 
    eqSum (PCons _ ps) (SThere f) (SThere g) = eqSum ps f g 
    eqSum _ SHere{} SThere{} = LT 
    eqSum _ SThere{} SHere{} = GT 

mapSumC :: forall c f g xs . (All (c &.> f) xs) => Proxy c -> (forall x . c (f x) => f x -> g x) -> Sum f xs -> Sum g xs 
mapSumC _ k s0 = go (mkProdC (Proxy :: Proxy (c &.> f)) Holds) s0 where 
  go :: forall xs0 . Prod (Holds (c &.> f)) xs0 -> Sum f xs0 -> Sum g xs0 
  go PNil x = case x of {} 
  go (PCons Holds _) (SHere a) = SHere (k a) 
  go (PCons _ xs) (SThere a) = SThere $ go xs a 

foldSum :: Sum (K x) xs -> x 
foldSum (SHere (K x)) = x 
foldSum (SThere x) = foldSum x 

instance All (Show &.> f) zs => Show (Sum f zs) where 
  show = foldSum . mapSumC (Proxy :: Proxy Show) (K . show) 
  

class Member x xs where 
  inj :: f x -> Sum f xs 
  prj :: Sum f xs -> Maybe (f x) 
  isMember :: Sum ((:~:) x) xs 

instance {-# OVERLAPS #-} Member x (x ': xs) where 
  inj = SHere 
  prj (SHere x) = Just x 
  prj SThere{} = Nothing 
  isMember = SHere Refl 

instance Member x xs => Member x (y ': xs) where 
  inj = SThere . inj 
  prj (SThere x) = prj x 
  prj SHere{} = Nothing 
  isMember = SThere isMember 

pattern SumElem x <- (prj -> Just x) 
  where SumElem x = inj x 

-- The constraint `All c xs' holds exactly when `c x' holds for all `x' in `xs'
class All (c :: k -> Constraint) (xs :: [k]) where   
  mkProdC :: Proxy c -> (forall a . c a => p a) -> Prod p xs 

instance All (c :: k -> Constraint) '[] where mkProdC _ _ = PNil 
instance (All c xs, c x) => All c (x ': xs) where mkProdC pr k = PCons k (mkProdC pr k) 

-- non emtpy list predicate
type family NonEmpty (xs :: [k]) :: Constraint where 
  NonEmpty (x ': xs) = () 

-- `x' is an element of `xs' if there exists a `y' in `xs' such that it is equal
-- to `x'
newtype Elem (x :: k) (xs :: [k]) = MkElem { getElem :: Sum ((:~:) x) xs }

type family IsElem (x :: k) (xs :: [k]) :: Constraint where 
  IsElem x (x ': xs) = () 
  IsElem x (y ': xs) = IsElem x xs 

-- Also known as flip 
newtype AppliedTo (x :: k) (f :: k -> *) = Ap (f x) 
newtype Flip (f :: k0 -> k1 -> *) (x :: k1) (y :: k0) = Flp (f y x)

newtype (:.:) (f :: k1 -> *) (g :: k0 -> k1) x = Cmp { unCmp :: f (g x) }
data (:*:) (f :: k0 -> *) (g :: k0 -> *) (x :: k0) = (:*:) (f x) (g x)
newtype K a (x :: k) = K { unK :: a } 
newtype Id a = Id { unId :: a } 

-- Type level AND 
type family (&&) (x :: Bool) (y :: Bool) :: Bool where 
  'False && x = 'False 
  x && 'False = 'False 
  'True && 'True = 'True 

(|&&) :: SingT a -> SingT b -> SingT (a && b)
SFalse |&& _ = SFalse 
_ |&& SFalse = SFalse 
STrue |&& STrue = STrue 
x |&& y = impossible  "Bool not {T,F}" (x, y) 

type family And (xs :: [Bool]) :: Bool where 
  And '[] = 'True 
  And (x ': xs) = x && And xs 

and_t :: SingT xs -> SingT (And xs)
and_t (SingT WNil) = STrue 
and_t (SingT (WCons x xs)) = SingT x |&& and_t (SingT xs)


-- Symbol 

type family RecAssocs (xs :: [RecLabel a b]) :: [b] where 
  RecAssocs '[] = '[] 
  RecAssocs ((nm ::: ty) ': xs) = ty ': RecAssocs xs

type family RecLabels (xs :: [RecLabel a b]) :: [a] where 
  RecLabels '[] = '[] 
  RecLabels ((nm ::: ty) ': xs) = nm ': RecLabels xs

type family CaseOrdering (x :: Ordering) (a :: k) (b :: k) (c :: k) :: k where 
  CaseOrdering 'LT a b c = a 
  CaseOrdering 'EQ a b c = b 
  CaseOrdering 'GT a b c = c 


{-
type family IsNotElem (xs :: [k]) (x :: k) :: Constraint where 
  IsNotElem '[] x = () 
  IsNotElem (x ': xs) y = ((x == y) ~ 'False, IsNotElem xs y)
-} 

-- A primitive inequality predicate which reduces. 
class NotEqual (x :: k) (y :: k) where 
  notEqual :: Not (x :~: y)

instance Never => NotEqual x x where notEqual = case is_falsum of 
instance NotEqual x y where notEqual = mapNeg (\x -> impossible  "not equal" x) triviallyTrue

neq_is_neq :: Not (x :~: y) -> Dict (NotEqual x y)
neq_is_neq x = x `seq` unsafeCoerce (Dict :: Dict ())

not_equal_does_not_reduce :: NotEqual a b => a :~: b -> () 
not_equal_does_not_reduce Refl = () 

-- The constraint which is never satisfied  
type family Never' :: k where 
  Never' = ('() :: ()) 
type Never = (Never' :: Constraint)

is_falsum :: Never => Void 
is_falsum = impossible  "is_falsum was called" () 

type family IsNotElem (xs :: [k]) (x :: k) :: Constraint where 
  IsNotElem '[] x = () 
  IsNotElem (x ': xs) y = (NotEqual x y, IsNotElem xs y)

type family IsSetRec_ (xs :: [RecLabel a b]) (seen :: [a]) :: Constraint where 
  IsSetRec_ '[] s = ()  
  IsSetRec_ ( (a ::: t0) ': r) seen = 
    (IsNotElem seen a, IsSetRec_ r (a ': seen))

type family IsSetRec (xs :: [RecLabel a b]) :: Constraint where 
  IsSetRec xs = IsSetRec_ xs '[] 

data NotElem (xs :: [k]) (x :: k) where 
  NotElem_Nil :: NotElem '[] x 
  NotElem_Cons :: !(Not (x :~: y)) -> !(NotElem xs y) -> NotElem (x ': xs) y 

data SetRec_ (seen :: [a]) (xs :: [RecLabel a b]) where 
  SetRec_Nil :: SetRec_ s '[] 
  SetRec_Cons :: !(NotElem seen a) -> !(SetRec_ (a ': seen) r) -> SetRec_ seen ((a ::: t0) ': r) 

instance NFData (NotElem a b) where rnf x = x `seq` () 
instance NFData (SetRec_ a b) where rnf x = x `seq` ()  

type SetRec = SetRec_ '[] 

openSetRec :: forall xs r0 . (SingKind ('KProxy :: KProxy k)) => SetRec (xs :: [RecLabel k k']) -> (IsSetRec xs => r0) -> r0
openSetRec = openSetRec_ where 
  openSetRec_ :: forall seen ys r . (SingKind ('KProxy :: KProxy k)) => SetRec_ seen (ys :: [RecLabel k k']) -> (IsSetRec_ ys seen => r) -> r
  openSetRec_ SetRec_Nil k = k 
  openSetRec_ (SetRec_Cons x xs) k = openNotElem x $ openSetRec_ xs k 
 
  openNotElem :: forall qs q r . NotElem (qs :: [k]) (q :: k) -> (IsNotElem qs q => r) -> r 
  openNotElem NotElem_Nil k = k 
  openNotElem (NotElem_Cons x xs) k = 
    case neq_is_neq x of { Dict -> 
    openNotElem xs k }

decNotElem :: (SingKind ('KProxy :: KProxy a)) => SingT (xs :: [a]) -> SingT (x :: a) -> Dec (NotElem xs x) 
decNotElem (SingT WNil) _ = Yes NotElem_Nil 
decNotElem (SingT (WCons (x :: SingWitness 'KProxy x0 t0) (xs :: SingWitness 'KProxy xs0 ts0))) e = 
  case (decNotElem (SingT xs) e, SingT x %== e) of 
    (Yes p, No q) -> Yes (NotElem_Cons q p) 
    (No p, _) -> No (mapNeg (\case { NotElem_Cons _ q -> q ; a -> impossible  "NotElem of (:) is not NotElem_Cons" a }) p) 
    (_, Yes Refl) -> No $ mapNeg (\case { (NotElem_Cons p _) -> case elimNeg p Refl of{} 
                                        ; a -> impossible  "NotElem of (:) is not NotElem_Cons" a })
                          triviallyTrue 

decSetRec :: forall xs . (SingKind ('KProxy :: KProxy a)) => SingT (xs :: [RecLabel a b]) -> Dec (SetRec xs)
decSetRec = go (SingT WNil) where 
  go :: forall (ys :: [RecLabel a b]) seen . SingT seen -> SingT ys -> Dec (SetRec_ seen ys) 
  go _seen (SingT WNil) = Yes SetRec_Nil
  go seen@(SingT seen') (SingT (WCons (WRecLabel wnm _wty) xs)) = 
    case (decNotElem seen (SingT wnm), go (SingT (WCons wnm seen')) (SingT xs)) of 
      (Yes p, Yes q) -> Yes (SetRec_Cons p q) 
      (No p, _) -> No (mapNeg (\case { SetRec_Cons x0 _ -> x0
                                     ; a -> impossible "SetRec of a (:) is not SetRec_Cons" a }) p) 
      (_, No p) -> No (mapNeg (\case { SetRec_Cons _ x0 -> x0
                                     ; a -> impossible "SetRec of a (:) is not SetRec_Cons" a }) p) 

type family IsJust (x :: Maybe k) :: k where 
  IsJust ('Just x) = x 

-- Lookup a value in a list of rec labels 
type family LookupRec (xs :: [RecLabel Symbol k]) (x :: Symbol) :: k where 
  LookupRec xs x = IsJust (LookupRecM xs x)
--   LookupRec ( (nm ::: ty) ': rest ) nm' = CaseOrdering (TL.CmpSymbol nm nm') (LookupRec rest nm') ty (LookupRec rest nm') 

type family LookupRecM (xs :: [RecLabel Symbol k]) (x :: Symbol) :: Maybe k where 
  LookupRecM '[] nm = 'Nothing 
  LookupRecM ( (nm ::: ty) ': rest ) nm' = CaseOrdering (TL.CmpSymbol nm nm') (LookupRecM rest nm') ('Just ty) (LookupRecM rest nm') 

lookupRecM :: forall (xs :: [RecLabel Symbol k]) (x :: Symbol) . SingT xs -> SingT x -> SingT (LookupRecM xs x)
lookupRecM (SingT xs0) (SingT x0) = go xs0 x0 where 
  go :: forall (xs' :: [RecLabel Symbol k]) (x' :: Symbol) x_rep x_rep1 
      . SingWitness 'KProxy xs' x_rep -> SingWitness 'KProxy x' x_rep1 -> SingT (LookupRecM xs' x')
  go WNil _ = SingT WNothing 
  go (WCons (WRecLabel (WSymbol nm') ty) xs) nms@(WSymbol nm) = 
    elimSingT (compareSymbol nm' nm) $ \case 
      WLT -> go xs nms 
      WEQ -> SingT (WJust ty) 
      WGT -> go xs nms 
      

type family LookupIx (xs :: [k]) (i :: TL.Nat) :: k where 
  LookupIx ( x ': xs ) 0 = x 
  LookupIx ( x ': xs ) n = LookupIx xs (n TL.- 1)

lookupRec :: forall (xs :: [RecLabel Symbol b]) (nm :: Symbol) (r :: b) . (LookupRec xs nm ~ r) => SingT xs -> SingT nm -> SingT r 
lookupRec row nm = 
  elimSingT (lookupRecM row nm) $ \case 
    WJust r -> SingT r 
    WNothing -> impossible "LookupRec exists but is not Just" () 


-- records to/from lists 
type family ZipRec (xs :: [a]) (ys :: [b]) :: [RecLabel a b] where 
  ZipRec '[] '[] = '[] 
  ZipRec (x ': xs) (y ': ys) = (x ::: y) ': ZipRec xs ys 
 
unzipRec :: SingT xs -> ( SingT (RecLabels xs) , SingT (RecAssocs xs) )
unzipRec (SingT WNil) = (SingT WNil, SingT WNil) 
unzipRec (SingT (WCons (WRecLabel a b) xs)) = 
  case unzipRec (SingT xs) of { (SingT as, SingT bs) -> (SingT (WCons a as), SingT (WCons b bs)) } 

recAssocs :: SingT xs -> SingT (RecAssocs xs) 
recAssocs = snd . unzipRec

recLabels :: SingT xs -> SingT (RecLabels xs)  
recLabels = fst . unzipRec 


-- Type level if. Note that this is STRICT 
type family If (a :: Bool) (x :: k)(y :: k) :: k where 
  If 'True x y = x 
  If 'False x y = y 

-- If forms an applicative of sorts  
newtype IfA (c :: Bool) (x :: *) (y :: *) = IfA { getIfA :: If c x y } 

if_pure :: forall a b cond . Sing cond => a -> b -> IfA cond a b 
if_pure a b = IfA $ 
  elimSingT (sing :: SingT cond) $ \case 
    WTrue -> a 
    WFalse -> b 

if_ap :: forall a b a' b' cond. Sing cond => IfA cond (a -> a') (b -> b') -> IfA cond a b -> IfA cond a' b' 
if_ap (IfA f) (IfA a) = IfA $ 
  elimSingT (sing :: SingT cond) $ \case 
    WTrue -> f a 
    WFalse -> f a 

-- Conjunction of constraints. 
class (x,y) => (&*&) (x :: Constraint) (y :: Constraint) 
instance (x,y) => x &*& y 

-- Composition of a constraint with a function 
class (c (f x)) => (&.>) (c :: k' -> Constraint) (f :: k -> k') (x :: k) 
instance (c (f x)) => (&.>) (c :: k' -> Constraint) (f :: k -> k') (x :: k) 

-- uncurry

class Uncurry f args o r | f args o -> r where 
  uncurryN :: (Prod f args -> f o) -> r 
  curryN :: r -> Prod f args -> f o 

instance (f o ~ r) => Uncurry f '[] o r where 
  uncurryN f = f PNil 
  curryN x PNil = x 

instance (Uncurry f args o r, q ~ (f arg -> r)) => Uncurry f (arg ': args) o q where 
  uncurryN f arg = uncurryN (f . PCons arg) 
  curryN f (PCons x xs) = curryN (f x) xs 

-- fresh names

freshName :: String -> Int -> String 
freshName nm count = nm ++ show count

locally :: MonadState a m => (a -> a) -> m x -> m x 
locally a go = get >>= \s0 -> put (a s0) >> go >>= \x -> put s0 >> return x 
