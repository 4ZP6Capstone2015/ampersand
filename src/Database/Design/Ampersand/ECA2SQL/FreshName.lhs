\begin{code}

{-# LANGUAGE StandaloneDeriving, TupleSections, GeneralizedNewtypeDeriving, UndecidableInstances, DefaultSignatures #-} 

module Database.Design.Ampersand.ECA2SQL.FreshName where 

import Numeric.Natural 
import qualified Data.Map as M 
import Control.Monad.State 
import Control.Monad.Reader  
import Control.Monad.Writer hiding (Sum(..), All(..))
import Control.Applicative 
import qualified Data.Set as S 
import Data.Functor.Identity  

import Database.Design.Ampersand.ECA2SQL.Utils 


\end{code}
A fresh name generator is a function which takes a name, and the number of
occurences of that name in the current context, producing a new name.
The new name is required to be distinct from the old name if and only if 
the number of occurences is not zero. 
\begin{code}
newtype FreshNameGen nm = FreshNameGen { instFresh :: nm -> Natural -> nm } 

\end{code}
The \lstinline{FreshNameT} monad transformer itself is just a composition 
of a reader monad and a state monad. Unfortunately, this means that we 
cannot use Generalized Newtype Deriving to automatically generate these 
instances. 
\begin{code}
newtype FreshNameT nms m a 
  = FreshNameT { unFreshT :: ReaderT (Prod FreshNameGen nms) 
                             (StateT (M.Map (Sum Id nms) Natural) m) 
                             a }

    deriving (Monad, Applicative, Functor, MonadPlus, Alternative, MonadWriter s) 

\end{code}
Standard helper types and functions.
\begin{description}
\item[\texttt{FreshName}] Insantiates the base monad to \lstinline{Identity}. 
\item[\texttt{runFreshNameT}] Given a fresh name generator, run a fresh name computation  
  with that function. A single fresh name computation can be instantiated with multiple 
  different generators. 
\item[\texttt{runFreshNameT}] Same as above, but instantiates the base monad to \lstinline{Identity}, 
  and removes such trivial occurences in the input and result types. 
\end{description}
\begin{code}
type FreshName x = FreshNameT x Identity 

runFreshNameT :: Monad m => Prod FreshNameGen nms -> FreshNameT nms m a -> m a
runFreshNameT f (FreshNameT k) = evalStateT (runReaderT k f) M.empty 

runFreshName :: Prod FreshNameGen nms -> FreshName nms a -> a
runFreshName f x = runIdentity $ runFreshNameT f x 

\end{code}
Sometimes you really just need to generate one name given some set of ``bound'' names. 
This function doesn't really have anything to do with the \lstinline{FreshNameT} monad
transformer, and can just as easily be implemented without it.
\begin{code}

deriving instance Eq a => Eq (Id a) 
deriving instance Ord a => Ord (Id a) 

singleFreshNm :: (Ord nm, Foldable f) => FreshNameGen nm -> f nm -> nm -> nm 
singleFreshNm gen nms nm = runFreshName (PCons gen PNil) (bindNames (foldMap (S.singleton . inj . Id) nms) >> makeFresh nm)

\end{code}
Standard type class instances which we cannot derive. 
\begin{code}
instance MonadState s m => MonadState s (FreshNameT nm m) where 
  state = lift . state 

instance MonadReader s m => MonadReader s (FreshNameT nm m) where 
  ask = lift ask 
  local f (FreshNameT (ReaderT k)) = FreshNameT $ ReaderT (local f . k) 

instance MonadTrans (FreshNameT nm) where 
  lift ac = FreshNameT $ ReaderT $ const $ StateT $ \x -> (,x) `liftM` ac 

\end{code}
A type class in the style of \texttt{mtl} monads. This allows the 
fresh name generator to reside at any level of a monad transformer stack. 

The default definitions for the functions are in terms of the the \lstinline{MonadTrans}
typeclass, which allows for default definitions for most monads. 
\begin{code}

class Monad m => MonadFresh (s :: [*]) (m :: * -> *) | m -> s where
  makeFresh :: Member x s => x -> m x 
  default makeFresh :: (MonadTrans t, MonadFresh s m, Monad m, Monad (t m), Member x s) => x -> t m x 
  makeFresh = lift . makeFresh 

  bindNames :: S.Set (Sum Id s) -> m () 
  default bindNames :: (MonadTrans t, MonadFresh s m, Monad m, Monad (t m)) => S.Set (Sum Id s) -> t m () 
  bindNames = lift . bindNames


\end{code}
Instances for some of the standard monad transformers found in \texttt{mtl}. 
\begin{code}

instance (Monoid w, MonadFresh s m) => MonadFresh s (WriterT w m) 
instance (MonadFresh s m) => MonadFresh s (ReaderT w m) 
instance (MonadFresh s m) => MonadFresh s (StateT w m) 

\end{code}
An instance for the \texttt{FreshNameT} monad transformer. This is the only part of this 
module which really ``does anything'' -- the rest is just plumbing. This style, however,
allows one to save a lot of boilerplate down the line, and makes writing easily composable code
almost trivial. 
\begin{code}

selectGen :: Member x nms => Prod FreshNameGen nms -> x -> Natural -> x
selectGen = go isMember where 
  go :: Sum ((:~:) x) nms -> Prod FreshNameGen nms -> x -> Natural -> x
  go (SHere Refl) (PCons gen _) = instFresh gen 
  go (SThere p) (PCons _ gens) = go p gens 
  go q PNil = case q of {} 
                       
instance (Monad m, All (Ord &.> Id) nms) => MonadFresh nms (FreshNameT nms m) where 
  bindNames nms = FreshNameT $ ReaderT $ const $ modify $ flip M.union (M.fromSet (const 0) nms)
  makeFresh x' = 
    let x = inj (Id x') 
        x :: Sum Id nms 
    in 
    FreshNameT $ ReaderT $ \gen -> StateT $ \nms -> 
      case M.lookup x nms of 
        Nothing -> return (x', M.insert x 0 nms)
        Just c  -> let c' = c+1
                   in c' `seq` return (selectGen gen x' c, M.insert x c' nms)


 
\end{code}
