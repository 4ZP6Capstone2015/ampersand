{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE ViewPatterns, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

-- Various utilities used by ECA2SQL 

module Database.Design.Ampersand.ECA2SQL.Utils 
  ( module Database.Design.Ampersand.ECA2SQL.Utils 
  , module GHC.TypeLits 
  , module Data.Proxy
  , module GHC.Exts
  , module Data.Type.Equality
  , module Database.Design.Ampersand.ECA2SQL.Equality 
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
import Database.Design.Ampersand.ECA2SQL.Trace 
import Control.DeepSeq

instance IsString Name where fromString = Name 

-- Given a functor `f', `Prod f' constructs the n-ary product category of `f'
data Prod (f :: k -> *) (xs :: [k]) where 
  PNil :: Prod f '[] 
  PCons :: f x -> Prod f xs -> Prod f (x ': xs) 

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
data AppliedTo (x :: k) (f :: k -> *) where Ap :: f x -> x `AppliedTo` f 

data Flip (f :: k0 -> k1 -> *) (x :: k1) (y :: k0) where 
  Flp :: f y x -> Flip f x y

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
x |&& y = impossible assert "Bool not {T,F}" (x `seq` y `seq` () )

type family And (xs :: [Bool]) :: Bool where 
  And '[] = 'True 
  And (x ': xs) = x && And xs 

and_t :: SingT xs -> SingT (And xs)
and_t (SingT WNil) = STrue 
and_t (SingT (WCons x xs)) = SingT x |&& and_t (SingT xs)


-- Symbol 
symbolKindProxy = Proxy :: Proxy ('KProxy :: KProxy Symbol)

compareSymbol' :: SingT (x :: Symbol) -> SingT y -> SingT (TL.CmpSymbol x y)
compareSymbol' (SingT (WSymbol x)) (SingT (WSymbol y)) = compareSymbol x y  

compareSymbol :: forall x y . (TL.KnownSymbol x, TL.KnownSymbol y) => Proxy x -> Proxy y -> SingT (TL.CmpSymbol x y)
compareSymbol x y =  
  let rf :: TL.CmpSymbol x y :~: TL.CmpSymbol x y 
      rf = Refl 
  in case compare (TL.symbolVal x) (TL.symbolVal y) of 
       LT -> case unsafeCoerce rf :: TL.CmpSymbol x y :~: 'LT of { Refl -> SLT }
       EQ -> case unsafeCoerce rf :: TL.CmpSymbol x y :~: 'EQ of { Refl -> SEQ }
       GT -> case unsafeCoerce rf :: TL.CmpSymbol x y :~: 'GT of { Refl -> SGT }

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
instance NotEqual x y where notEqual = mapNeg (\x -> impossible assert "not equal" x) triviallyTrue

neq_is_neq :: Not (x :~: y) -> Dict (NotEqual x y)
neq_is_neq x = x `seq` unsafeCoerce (Dict :: Dict ())

not_equal_does_not_reduce :: NotEqual a b => a :~: b -> () 
not_equal_does_not_reduce Refl = () 

-- The constraint which is never satisfied  
type family Never' :: k where 
  Never' = ('() :: ()) 
type Never = (Never' :: Constraint)

is_falsum :: Never => Void 
is_falsum = impossible assert "is_falsum was called" () 

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
    (No p, _) -> No (mapNeg (\case { NotElem_Cons _ q -> q ; a -> impossible assert "NotElem of (:) is not NotElem_Cons" a }) p) 
    (_, Yes Refl) -> No $ mapNeg (\case { (NotElem_Cons p _) -> case elimNeg p Refl of{} 
                                        ; a -> impossible assert "NotElem of (:) is not NotElem_Cons" a })
                          triviallyTrue 

decSetRec :: forall xs . (SingKind ('KProxy :: KProxy a)) => SingT (xs :: [RecLabel a b]) -> Dec (SetRec xs)
decSetRec = go (SingT WNil) where 
  go :: forall (ys :: [RecLabel a b]) seen . SingT seen -> SingT ys -> Dec (SetRec_ seen ys) 
  go _seen (SingT WNil) = Yes SetRec_Nil
  go seen@(SingT seen') (SingT (WCons (WRecLabel wnm _wty) xs)) = 
    case (decNotElem seen (SingT wnm), go (SingT (WCons wnm seen')) (SingT xs)) of 
      (Yes p, Yes q) -> Yes (SetRec_Cons p q) 
      (No p, _) -> No (mapNeg (\case { SetRec_Cons x0 _ -> x0
                                     ; a -> impossible assert "SetRec of a (:) is not SetRec_Cons" (a `seq` ()) }) p) 
      (_, No p) -> No (mapNeg (\case { SetRec_Cons _ x0 -> x0
                                     ; a -> impossible assert "SetRec of a (:) is not SetRec_Cons" (a `seq` ()) }) p) 

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
    WNothing -> impossible assert "LookupRec exists but is not Just" () 


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

-- uncurry

class Uncurry f args o r | f args o -> r where 
  uncurryN :: (Prod f args -> f o) -> r

instance (f o ~ r) => Uncurry f '[] o r where 
  uncurryN f = f PNil 

instance (Uncurry f args o r, q ~ (f arg -> r)) => Uncurry f (arg ': args) o q where 
  uncurryN f arg = uncurryN (f . PCons arg) 

-- fresh names

freshName :: String -> Int -> String 
freshName nm count = nm ++ show count


