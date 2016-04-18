{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

{-# OPTIONS_GHC -fno-cse #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-float-in #-}

module Database.Design.Ampersand.ECA2SQL.Singletons  where 

import Control.Applicative 
import Unsafe.Coerce 
import Data.Proxy (Proxy(..), KProxy(..))
import GHC.TypeLits (Symbol, symbolVal, sameSymbol, KnownSymbol)
import qualified GHC.TypeLits as TL  
import Database.Design.Ampersand.ECA2SQL.Equality 
import Database.Design.Ampersand.Basics.Assertion
import Numeric.Natural
import Control.DeepSeq

-- test

testval0 = sing :: SingT '( 'Just 10, '[ "x", "y" ] ) 

--

withSingT :: forall (x :: k) r . (SingKind ('KProxy :: KProxy k)) => SingT x -> (Sing x => Proxy x -> r) -> r
withSingT (SingT a) k = withSingW a k

singFromProxy :: Sing x => Proxy x -> SingT x 
singFromProxy Proxy = sing 

data TyRep = TyCtr Symbol [TyRep] 
           | TyPrimNat TL.Nat  -- represents types by constructure and list of arguments; Natural numbers and strings of type level, use type level strings to label tables; Nat = natural numbers
           | TyPrimSym TL.Symbol -- Sym = Symbol, type literals, strings; GHCI supports literals and comparisons associated with those literals

-- Generic singleton class, defining singletons for a kind in terms of 
-- an isomorphism between that type and a TyRep. 
class (kp ~ 'KProxy) => SingKind (kp :: KProxy k) where 
  data SingWitness kp :: k -> TyRep -> *
  
  withSingW :: forall (x :: k) r xr . SingWitness kp x xr -> (Sing x => Proxy x -> r) -> r

  -- proof that each witness produces a rep of the correct type. 
  witness :: SingWitness kp x xr -> (TyRepOf x :~: xr, Dict (TyRepSingI xr))
  --
 
  -- Proof of the isomorphism. The default implementation uses unsafeCoerce,
  -- which will work only if everything is defined properly, perhaps there is a
  -- good way of making that explicit.
  singKindWitness1 :: forall ty0 ty1 rep0 rep1 . rep0 :~: rep1
                   -> SingWitness kp ty0 rep0 
                   -> SingWitness kp ty1 rep1 
                   -> ty0 :~: ty1 
  -- singKindWitness1 x a b = a `seq` b `seq` safeCoerce "sing1" x 
  singKindWitness1 x a b = x `seq` a `seq` b `seq` unsafeCoerce (Refl :: ty0 :~: ty0) 

  singKindWitness2 :: forall ty0 ty1 rep0 rep1 . ty0 :~: ty1 
                   -> SingWitness kp ty0 rep0 
                   -> SingWitness kp ty1 rep1 
                   -> rep0 :~: rep1
  -- singKindWitness2 x a b = a `seq` b `seq` safeCoerce "sing2" x 
  singKindWitness2 x a b = x `seq` a `seq` b `seq` unsafeCoerce (Refl :: rep0 :~: rep0)

  type ValOfSing (kp :: KProxy k)  

  sing2val' :: forall (x :: k) xr . SingWitness kp x xr -> ValOfSing kp 
  val2sing' :: forall r . Proxy kp -> ValOfSing kp -> (forall (x :: k) xr . SingWitness kp x xr -> r) -> r

sing2val :: forall (x :: k) . (SingKind ('KProxy :: KProxy k)) => SingT x -> ValOfSing (KindOf x)
sing2val (SingT x) = sing2val' x 

val2sing :: forall r kp . (kp ~ ('KProxy :: KProxy k), SingKind kp) => Proxy kp -> ValOfSing kp -> (forall (x :: k) . SingT x -> r) -> r
val2sing pr x k = val2sing' pr x (k . SingT) 

tyRepOfW :: TyRepSingI rep => SingWitness kp k rep -> TyRepSing rep
tyRepOfW _ = tyRepSing

type KindOf (x :: k) = ('KProxy :: KProxy k) 

type family TyRepOf (x :: k) :: TyRep

class WitnessSingI (x :: k) where 
  witnessSing :: SingWitness ('KProxy :: KProxy k) x (TyRepOf x) 

-- The TyRep singleton
data family TyRepSing (x :: k) 

data instance TyRepSing (x :: [TyRep]) where 
  STyNil :: TyRepSing ('[] :: [TyRep])
  STyCons :: !(TyRepSing (x :: TyRep)) -> !(TyRepSing xs) -> TyRepSing (x ': xs) 

data instance TyRepSing (x :: TyRep) where 
  STyCtr :: (TL.KnownSymbol nm) => !(Proxy nm) -> !(TyRepSing args) -> TyRepSing ('TyCtr nm args) 
  STySym :: (TL.KnownSymbol nm) => !(Proxy nm) -> TyRepSing ('TyPrimSym nm) 
  STyNat :: (TL.KnownNat n) => !(Proxy n) -> TyRepSing ('TyPrimNat n) 
  
class TyRepSingI (x :: k) where 
  tyRepSing :: TyRepSing x 

instance TyRepSingI ('[] :: [TyRep]) where tyRepSing = STyNil 
instance (TyRepSingI x, TyRepSingI xs) => TyRepSingI ((x :: TyRep) ': xs) where tyRepSing = STyCons tyRepSing tyRepSing
instance (TL.KnownNat n) => TyRepSingI ('TyPrimNat n) where tyRepSing = STyNat Proxy 
instance (TL.KnownSymbol n) => TyRepSingI ('TyPrimSym n) where tyRepSing = STySym Proxy 
instance (TyRepSingI (x :: [TyRep]), TL.KnownSymbol nm) => TyRepSingI ('TyCtr nm x) where tyRepSing = STyCtr Proxy tyRepSing

-- Decide if twos symbols are the same
eqSymbol :: (TL.KnownSymbol x, TL.KnownSymbol y) => Proxy x -> Proxy y -> DecEq x y 
eqSymbol x y = 
  case TL.sameSymbol x y of 
    Just a  -> Yes a
    Nothing -> No $ mapNeg (\case { Refl -> impossible "eqSymbol" () }) triviallyTrue

eqProdTypRep :: TyRepSing (xs :: [TyRep]) -> TyRepSing ys -> DecEq xs ys 
eqProdTypRep STyNil STyNil = Yes Refl
eqProdTypRep STyNil STyCons{} = No $ mapNeg (\case {}) triviallyTrue 
eqProdTypRep STyCons{} STyNil = No $ mapNeg (\case {}) triviallyTrue 
eqProdTypRep (STyCons x xs) (STyCons y ys) = 
  case eqTyRep x y of 
    No p -> No $ mapNeg (\case { Refl -> Refl }) p
    Yes Refl -> 
      case eqProdTypRep xs ys of 
        Yes Refl -> Yes Refl 
        No p -> No $ mapNeg (\case { Refl -> Refl }) p

eqTyRep :: TyRepSing (x :: TyRep) -> TyRepSing y -> DecEq x y 
eqTyRep (STyNat n0) (STyNat n1) =
  case TL.sameNat n0 n1 of 
    Just Refl -> Yes Refl
    Nothing   -> No $ mapNeg (\case { Refl -> impossible "eqTyRep:TyNat" () }) triviallyTrue

eqTyRep (STySym n0) (STySym n1) = mapDec (cong Refl) (mapNeg (\case {Refl -> Refl})) $ eqSymbol n0 n1 

eqTyRep (STyCtr nm0 args0) (STyCtr nm1 args1) = 
  case eqSymbol nm0 nm1 of 
    No p -> No $ mapNeg (\case {Refl -> Refl}) p
    Yes Refl -> 
      case eqProdTypRep args0 args1 of 
        Yes Refl -> Yes Refl 
        No p -> No $ mapNeg (\case {Refl -> Refl}) p

   -- {} is wild card for large data structures, or large records 
eqTyRep STySym{} STyCtr{} = No $ mapNeg (\case {}) triviallyTrue
eqTyRep STyCtr{} STySym{} = No $ mapNeg (\case {}) triviallyTrue
eqTyRep STyNat{} STyCtr{} = No $ mapNeg (\case {}) triviallyTrue
eqTyRep STyCtr{} STyNat{} = No $ mapNeg (\case {}) triviallyTrue 
eqTyRep (STySym _) (STyNat _) = No $ mapNeg (\case {}) triviallyTrue 
eqTyRep (STyNat _) (STySym _) = No $ mapNeg (\case {}) triviallyTrue 
    
-- Singletons of some kind in terms of their type rep. Using the constructor is safe. 
data SingT (x :: k) where  
  SingT :: !(SingWitness ('KProxy :: KProxy k) (x :: k) x_rep) -> SingT x -- singleton witnesses for that datatype; accepts value for any representation; construct in a way that invalid values are not possible

instance NFData (SingT x) where 
  rnf x = x `seq` () 

elimSingT :: SingT x -> (forall xr . SingWitness 'KProxy x xr -> r) -> r  -- x_rep is quantified, universally quantified function, given a sing witness of any representation type returns value r; passing in an arg that scrutinizes is invalid
elimSingT (SingT x) f = f x  -- exist f is the same as for all types a such that there is a type g to f

class (WitnessSingI x, TyRepSingI (TyRepOf x)) => Sing x where 
  sing :: SingT x 
instance (WitnessSingI x, TyRepSingI (TyRepOf x)) => Sing x where 
  sing = SingT witnessSing


-- You can compare singletons based on their type rep. 
(%==) :: SingKind ('KProxy :: KProxy k) => SingT (x :: k) -> SingT y -> DecEq x y 
(%==) (SingT x) (SingT y) = 
  case (witness x, witness y) of { ((Refl, Dict), (Refl, Dict)) -> 
  case eqTyRep (tyRepOfW x) (tyRepOfW y) of  --eqTyRep compares type reps, not the singleton 
    Yes p -> Yes $ singKindWitness1 p x y  -- proof of equality (p)
    No p -> No (mapNeg (\q -> singKindWitness2 q x y ) p) }  -- if types are equal; if two type reps are equal then the types are equal; Singleton needs representations of two types and decide of those representations are the same; uses kindWitness function to prove injectivity
-- %== decideable equality, if you have a value of singleton type; this function allows you to make arbitrary comparisons to it; e.g., when you construct a row, a name must be unique -- expressed at type level, list of names that carry type information such that when you pattern match on it, you gain type information; this give you the ability to write proofs using pattern matching; when you get the type returned
------- Basic types
-- Bool

type BoolKind = ('KProxy :: KProxy Bool)
boolKind = Proxy :: Proxy BoolKind 

instance SingKind ('KProxy :: KProxy Bool) where 
  data SingWitness ('KProxy :: KProxy Bool) x args where 
    WFalse :: SingWitness 'KProxy 'False ( TyRepOf 'False )
    WTrue  :: SingWitness 'KProxy 'True  ( TyRepOf 'True  )

  withSingW WFalse k = k Proxy 
  withSingW WTrue  k = k Proxy 

  witness WTrue = (Refl, Dict)
  witness WFalse = (Refl, Dict) 
{-
  singKindWitness1 Refl WTrue WTrue = Refl 
  singKindWitness1 Refl WFalse WFalse = Refl 

  singKindWitness2 a WTrue WFalse = case a of {}
  singKindWitness2 a WFalse WTrue = case a of {}
  singKindWitness2 _ WTrue WTrue = Refl 
  singKindWitness2 _ WFalse WFalse = Refl -}

  type ValOfSing ('KProxy :: KProxy Bool) = Bool   
  sing2val' = \case { WFalse -> False; WTrue -> True }  
  val2sing' _ val k = case val of { True -> k WTrue; False -> k WFalse } 

type instance TyRepOf 'False = 'TyCtr "Bool_False" '[]
type instance TyRepOf 'True = 'TyCtr "Bool_True" '[]

instance WitnessSingI 'True where witnessSing = WTrue 
instance WitnessSingI 'False where witnessSing = WFalse 

pattern SFalse = SingT WFalse 
pattern STrue = SingT WTrue



-- Ordering 
instance SingKind ('KProxy :: KProxy Ordering) where 
  data SingWitness ('KProxy :: KProxy Ordering) x args where 
    WLT  :: SingWitness 'KProxy 'LT ( TyRepOf 'LT )
    WEQ  :: SingWitness 'KProxy 'EQ ( TyRepOf 'EQ )
    WGT  :: SingWitness 'KProxy 'GT ( TyRepOf 'GT )

  withSingW WLT k = k Proxy 
  withSingW WEQ k = k Proxy 
  withSingW WGT k = k Proxy 

  witness = \case { WLT -> (Refl, Dict); WEQ -> (Refl, Dict); WGT -> (Refl, Dict) } 
{-
  singKindWitness1 Refl WLT WLT = Refl 
  singKindWitness1 Refl WEQ WEQ = Refl 
  singKindWitness1 Refl WGT WGT = Refl 

  singKindWitness2 _ WLT WLT = Refl 
  singKindWitness2 _ WEQ WEQ = Refl 
  singKindWitness2 _ WGT WGT = Refl -}

  type ValOfSing ('KProxy :: KProxy Ordering) = Ordering   
  sing2val' = \case { WLT -> LT; WEQ -> EQ; WGT -> GT }  
  val2sing' _ val k = case val of { LT -> k WLT; EQ -> k WEQ; GT -> k WGT }  

pattern SEQ = SingT WEQ 
pattern SLT = SingT WLT
pattern SGT = SingT WGT

type instance TyRepOf 'LT = 'TyCtr "Ordering_LT" '[]
type instance TyRepOf 'EQ = 'TyCtr "Ordering_EQ" '[]
type instance TyRepOf 'GT = 'TyCtr "Ordering_GT" '[]

instance WitnessSingI 'LT where witnessSing = WLT  
instance WitnessSingI 'EQ where witnessSing = WEQ 
instance WitnessSingI 'GT where witnessSing = WGT 


-- Tuple 
instance (SingKind ('KProxy :: KProxy a), SingKind ('KProxy :: KProxy b))
  => SingKind ('KProxy :: KProxy (a,b)) where 

    data SingWitness ('KProxy :: KProxy (a,b)) x args where 
      WTup2 :: !(SingWitness 'KProxy va arep) -> !(SingWitness 'KProxy vb brep) -- ! means strict field, difference between lazy and strict fields; if you know the substructure is strict then the entire thing becomes strict 
                -> SingWitness 'KProxy '((va :: a), (vb :: b)) ( 'TyCtr "(,)" '[ arep, brep ] )  
                    
    withSingW (WTup2 x y) k = withSingW x $ \_ -> withSingW y $ \_ -> k Proxy 

    witness (WTup2 a b) = 
      case (witness a, witness b) of { ((Refl, Dict), (Refl, Dict)) -> (Refl, Dict) } -- pattenr match and return trivial proof, the compiler know the proofs, you can return refl or dict; witness proves single returns type representation coorresponding to the type inside of it 
{-  
    singKindWitness1 Refl (WTup2 a b) (WTup2 a' b') = 
      case (singKindWitness1 Refl a a', singKindWitness1 Refl b b') of { (Refl, Refl) -> Refl }

    singKindWitness2 Refl (WTup2 a b) (WTup2 a' b') = 
      case (singKindWitness2 Refl a a', singKindWitness2 Refl b b') of { (Refl, Refl) -> Refl } -}
            
    type ValOfSing ('KProxy :: KProxy (a,b)) = (ValOfSing ('KProxy :: KProxy a), ValOfSing ('KProxy :: KProxy b))
    sing2val' (WTup2 a b) = (sing2val' a, sing2val' b) 
    val2sing' _ (a,b) k = val2sing' (Proxy :: Proxy ('KProxy :: KProxy a)) a $ \( a') -> 
                         val2sing' (Proxy :: Proxy ('KProxy :: KProxy b)) b $ \( b') -> 
                         k ( WTup2 a' b')

type instance TyRepOf '(a, b) = 'TyCtr "(,)" '[ TyRepOf a, TyRepOf b ]

instance (WitnessSingI a, WitnessSingI b) => WitnessSingI '(a, b) where witnessSing = WTup2 witnessSing witnessSing

-- List 
instance (SingKind ('KProxy :: KProxy k)) => SingKind ('KProxy :: KProxy [k]) where 
  data SingWitness ('KProxy :: KProxy [k]) x nm where 
    WNil :: SingWitness 'KProxy ('[] :: [k]) ( 'TyCtr "[]_[]" '[] )
    WCons :: !(SingWitness 'KProxy x xrep)
                -> !(SingWitness 'KProxy xs xsrep)
                -> SingWitness 'KProxy ((x :: k) ': xs) ( 'TyCtr "[]_:" '[ xrep, xsrep ] )

  withSingW WNil k = k Proxy 
  withSingW (WCons x y) k = withSingW x $ \_ -> withSingW y $ \_ -> k Proxy 

  witness WNil = (Refl, Dict)
  witness (WCons a b) = 
      case (witness a, witness b) of 
        ((Refl, Dict), (Refl, Dict)) -> (Refl, Dict) 
  {-
  singKindWitness1 Refl WNil WNil = Refl 
  singKindWitness1 a WCons{} WNil{} = case a of {} 
  singKindWitness1 a WNil{} WCons{} = case a of {} 
  singKindWitness1 Refl (WCons a b) (WCons a' b') = 
    cong2 Refl (singKindWitness1 Refl a a') (singKindWitness1 Refl b b') 

  singKindWitness2 Refl WNil WNil = Refl 
  singKindWitness2 a WCons{} WNil{} = case a of {} 
  singKindWitness2 a WNil{} WCons{} = case a of {} 
  singKindWitness2 Refl (WCons a b) (WCons a' b') = 
    cong2 Refl Refl $ cong2 Refl (singKindWitness2 Refl a a') $ cong2 Refl (singKindWitness2 Refl b b') Refl -}

  type ValOfSing ('KProxy :: KProxy [k]) = [ ValOfSing ('KProxy :: KProxy k) ]
  sing2val' WNil = []
  sing2val' (WCons x xs) = sing2val' x : sing2val' xs

  val2sing' _ [] k = k WNil 
  val2sing' kp (x:xs) k = val2sing' kp xs $ \xsv -> val2sing' Proxy x $ \xv -> k (WCons xv xsv)

type instance TyRepOf '[] = 'TyCtr "[]_[]" '[ ]
type instance TyRepOf (x ': xs) =  'TyCtr "[]_:" '[ TyRepOf x, TyRepOf xs ]

instance (WitnessSingI a, WitnessSingI b) => WitnessSingI (a ': b) where witnessSing = WCons witnessSing witnessSing
instance WitnessSingI '[] where witnessSing = WNil 

pattern SCons x xs = SingT (WCons x xs) 
pattern SNil = SingT WNil 

-- Maybe 
instance (SingKind ('KProxy :: KProxy k)) => SingKind ('KProxy :: KProxy (Maybe k)) where 
  data SingWitness ('KProxy :: KProxy (Maybe k)) x nm where 
    WNothing :: SingWitness 'KProxy ('Nothing :: (Maybe k)) ( 'TyCtr "Maybe_Nothing" '[] )
    WJust :: !(SingWitness 'KProxy x xrep)
                -> SingWitness 'KProxy ('Just x) ( 'TyCtr "Maybe_Just" '[ xrep ] )

  withSingW WNothing k = k Proxy 
  withSingW (WJust x) k = withSingW x $ \_ -> k Proxy 

  witness WNothing = (Refl, Dict) 
  witness (WJust a) = case witness a of { (Refl, Dict) -> (Refl, Dict) } 
{-
  singKindWitness1 Refl WNothing WNothing = Refl 
  singKindWitness1 a WNothing{} WJust{} = case a of {} 
  singKindWitness1 a WJust{} WNothing{} = case a of {} 
  singKindWitness1 Refl (WJust x) (WJust y) = case singKindWitness1 Refl x y of { Refl -> Refl } 
-}
  type ValOfSing ('KProxy :: KProxy (Maybe k)) = Maybe ( ValOfSing ('KProxy :: KProxy k) )

  sing2val' = \case { WNothing -> Nothing; WJust x -> Just (sing2val' x) } 
  
  val2sing' _ Nothing k = k WNothing 
  val2sing' _ (Just x) k = val2sing' Proxy x $ \q -> k (WJust q)

type instance TyRepOf 'Nothing ='TyCtr "Maybe_Nothing" '[] 
type instance TyRepOf ('Just x) = 'TyCtr "Maybe_Just" '[ TyRepOf x ]

instance (WitnessSingI a) => WitnessSingI ('Just a) where witnessSing = WJust witnessSing 
instance WitnessSingI 'Nothing where witnessSing = WNothing

-- Record label kind
data RecLabel a b = a ::: b

instance (SingKind ('KProxy :: KProxy a), SingKind ('KProxy :: KProxy b))
  => SingKind ('KProxy :: KProxy (RecLabel a b)) where 

    witness (WRecLabel a b) = case (witness a, witness b) of { ((Refl, Dict), (Refl, Dict)) -> (Refl, Dict) }
    
    withSingW (WRecLabel x y) k = withSingW x $ \_ -> withSingW y $ \_ -> k Proxy 

    data SingWitness ('KProxy :: KProxy (RecLabel a b)) x args where 
      WRecLabel :: !(SingWitness 'KProxy va arep) -> !(SingWitness 'KProxy vb brep)
                -> SingWitness 'KProxy ((va :: a) '::: (vb :: b)) ( 'TyCtr "RecLabel_:::" '[ arep, brep ] )
{-                      
    singKindWitness1 Refl (WRecLabel a b) (WRecLabel a' b') = 
      cong2 Refl (singKindWitness1 Refl a a') (singKindWitness1 Refl b b') 

    singKindWitness2 Refl (WRecLabel a b) (WRecLabel a' b') = 
      cong2 Refl Refl $ cong2 Refl (singKindWitness2 Refl a a') $ cong2 Refl (singKindWitness2 Refl b b') Refl 
-}

    type ValOfSing (('KProxy :: KProxy (RecLabel a b))) = RecLabel (ValOfSing ('KProxy :: KProxy a)) (ValOfSing ('KProxy :: KProxy b)) 
    val2sing' _ (a ::: b) k = val2sing' Proxy a $ \a' -> 
                              val2sing' Proxy b $ \b' -> 
                              k (WRecLabel a' b') 

    sing2val' = \case { WRecLabel a b -> sing2val' a ::: sing2val' b } 

type instance TyRepOf (a '::: b) = 'TyCtr  "RecLabel_:::" '[ TyRepOf a, TyRepOf b ]
instance (WitnessSingI a, WitnessSingI b) => WitnessSingI (a '::: b) where witnessSing = WRecLabel witnessSing witnessSing

pattern SRecLabel x y = SingT (WRecLabel x y)

-- Nat 
data Nat = Z | S Nat 

{-
data instance SingT (y :: Nat) where 
  SZ :: SingT 'Z 
  SS :: !(SingT n) -> SingT ('S n) 
type NatSing = (SingT :: Nat -> *)
instance Sing 'Z where sing = SZ 
instance Sing n => Sing ('S n) where sing = SS sing 


-- Type Level nat
data instance SingT (y :: TL.Nat) where 
  NatSingI :: (TL.KnownNat n) => !(Proxy n) -> SingT n 
-}

-- Symbol

instance SingKind ('KProxy :: KProxy Symbol) where 
  data SingWitness ('KProxy :: KProxy Symbol) x args where 
    WSymbol :: TL.KnownSymbol x => !(Proxy x) -> SingWitness 'KProxy x ( 'TyPrimSym x ) 

  withSingW (WSymbol x) k = k x

  witness WSymbol{} = (Refl, Dict) 

  type ValOfSing ('KProxy :: KProxy Symbol) = String 
  sing2val' (WSymbol x) = TL.symbolVal x 
  val2sing' _ str k = case TL.someSymbolVal str of { TL.SomeSymbol x -> k (WSymbol x) }

pattern SSymbol x = SingT (WSymbol x) 

type instance TyRepOf (a :: Symbol) = 'TyPrimSym a 
instance (TL.KnownSymbol a) => WitnessSingI a where witnessSing = WSymbol Proxy 

-- Nat 

instance SingKind ('KProxy :: KProxy TL.Nat) where 
  data SingWitness ('KProxy :: KProxy TL.Nat) x args where 
    WNat :: TL.KnownNat x => !(Proxy x) -> SingWitness 'KProxy x ( 'TyPrimNat x ) 

  withSingW (WNat x) k = k x 

  witness WNat{} = (Refl, Dict) 

  type ValOfSing ('KProxy :: KProxy TL.Nat) = Natural  
  sing2val' (WNat x) = fromIntegral $ TL.natVal x 
  val2sing' _ n k = case TL.someNatVal (fromIntegral n) of 
                     Just (TL.SomeNat x) -> k (WNat x)
                     Nothing -> impossible "negative natural number" () 

pattern SNat x = SingT (WNat x) 

type instance TyRepOf (a :: TL.Nat) = 'TyPrimNat a 
instance (TL.KnownNat a) => WitnessSingI a where witnessSing = WNat Proxy 
