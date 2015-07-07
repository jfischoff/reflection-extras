{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures#-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE CPP #-}
module Data.Reflection.Extras
   ( using
   , usingT
   , reifyInstance
   , with
   , Lift
   , ReifiableConstraint (..)
   , Reifies (..)
   , Def (..)
   , FromJSON (..)
   , ToJSON (..)
   ) where
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Monoid
import Data.Proxy
import Data.Reflection
import Control.Lens
import Data.Aeson
import Data.Aeson.Types
import Control.Applicative

#define REFLECT (reflect (Proxy :: Proxy s))

--------------------------------------------------------------------------------
-- Intro
-- I made this a functor to make the instances easier
newtype Lift (p :: * -> Constraint) (s :: *) (a :: *) = Lift { lower :: a }
   deriving (Functor)

instance Applicative (Lift p s) where
   pure              = Lift
   Lift f <*> Lift x = Lift $ f x

lift :: Iso' a (Lift p s a)
lift = iso Lift lower

newtype ProxyLift (p :: * -> Constraint) (a :: *) (s :: *) = PLift { plower :: a }

pLift :: Iso' a (ProxyLift p a s)
pLift = iso PLift plower

flipS :: Iso' (Lift p s a) (ProxyLift p a s)
flipS = from lift . pLift

class ReifiableConstraint p where
  data Def (p :: * -> Constraint) (a :: * ) :: *
  reifiedIns :: forall s a. Reifies s (Def p a) :- p (Lift p s a)
--  default reifiedIns :: forall s a. p (Lift p s a)
--                     => Reifies s (Def p a) :- p (Lift p s a)
--  reifiedIns = Sub (Dict :: Reifies s (Def p a)
--                         => Dict (p (Lift p s a)))

--------------------------------------------------------------------------------
-- Machinery


with :: forall p a. Def p a -> (forall s. Reifies s (Def p a) => Lift p s a) -> a
with d v = reify d (plower . asProxyOf (view flipS v))

reifyInstance :: Def p a -> (forall (s :: *). Reifies s (Def p a) => Proxy s -> r) -> r
reifyInstance = reify

asProxyOf :: f s -> Proxy s -> f s
asProxyOf a _ = a

-- | Choose a dictionary for a local type class instance.
--
--   >>> using (Monoid (+) 0) $ mempty <> 10 <> 12
--   > 12
--
using :: forall p a. ReifiableConstraint p => Def p a -> (p a => a) -> a
using d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def p a) :- p a
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: p (Lift p s a) :- p a
  in m \\ replaceProof

usingT :: forall p f a. ReifiableConstraint p => Def p a -> (p a => f a) -> f a
usingT d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def p a) :- p a
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: p (Lift p s a) :- p a
  in m \\ replaceProof

{-
-- ClassProxy
data ClassProxy (p :: * -> Constraint) = ClassProxy

given :: ClassProxy c -> p s -> a -> Lift c s a
given _ _ = Lift

eq :: ClassProxy Eq
eq = ClassProxy

ord :: ClassProxy Ord
ord = ClassProxy

monoid :: ClassProxy Monoid
monoid = ClassProxy
-}
--------------------------------------------------------------------------------
-- Instances


instance Reifies s (Def Enum a) => Enum (Lift Enum s a) where
   succ a               = Lift $ succ_     REFLECT (lower a)
   pred a               = Lift $ pred_     REFLECT (lower a)
   toEnum a             = Lift $ toEnum_   REFLECT a
   fromEnum a           =        fromEnum_ REFLECT $ lower a
   enumFrom       a     = map Lift $ enumFrom_       REFLECT (lower a)
   enumFromThen   a b   = map Lift $ enumFromThen_   REFLECT (lower a) (lower b)
   enumFromTo     a b   = map Lift $ enumFromTo_     REFLECT (lower a) (lower b)
   enumFromThenTo a b c = map Lift $ enumFromThenTo_ REFLECT (lower a) (lower b) (lower c)

instance ReifiableConstraint Enum where
  data Def Enum a = Enum
      { succ_           :: a -> a
      , pred_           :: a -> a
      , toEnum_         :: Int -> a
      , fromEnum_       :: a -> Int
      , enumFrom_       :: a -> [a]
      , enumFromThen_   :: a -> a -> [a]
      , enumFromTo_     :: a -> a -> [a]
      , enumFromThenTo_ :: a -> a -> a -> [a]
      }
  reifiedIns = Sub Dict

instance Reifies s (Def Bounded a) => Bounded (Lift Bounded s a) where
  minBound = Lift $ minBound_ REFLECT
  maxBound = Lift $ maxBound_ REFLECT

instance ReifiableConstraint Bounded where
  data Def Bounded a = Bounded
     { minBound_ :: a
     , maxBound_ :: a
     }
  reifiedIns = Sub Dict

instance Reifies s (Def Num a) => Num (Lift Num s a) where
  (+)         = liftA2 ((+.) REFLECT)
  (*)         = liftA2 ((*.) REFLECT)
  (-)         = liftA2 ((-.) REFLECT)
  negate      = fmap (negate_ REFLECT)
  abs         = fmap (abs_ REFLECT)
  signum      = fmap (signum_ REFLECT)
  fromInteger = Lift . fromInteger_  REFLECT

instance ReifiableConstraint Num where
  data Def Num a = Num
     { (+.)         :: a -> a -> a
     , (*.)         :: a -> a -> a
     , (-.)         :: a -> a -> a
     , negate_      :: a -> a
     , abs_         :: a -> a
     , signum_      :: a -> a
     , fromInteger_ :: Integer -> a
     }
  reifiedIns = Sub Dict

instance (Reifies s (Def Real a)) => Eq (Lift Real s a) where
   a == b = compare a b == EQ

instance (Reifies s (Def Real a)) => Ord (Lift Real s a) where
   compare a b = (compare_ . ordDef) REFLECT (lower a) (lower b)

instance (Reifies s (Def Real a)) => Num (Lift Real s a) where
   (+)         = liftA2 ((+.) $ numDef REFLECT)
   (*)         = liftA2 ((*.) $ numDef REFLECT)
   (-)         = liftA2 ((-.) $ numDef REFLECT)
   negate      = fmap (negate_ $ numDef REFLECT)
   abs         = fmap (abs_ $ numDef REFLECT)
   signum      = fmap (signum_ $ numDef REFLECT)
   fromInteger = Lift . (fromInteger_ . numDef) REFLECT

instance Reifies s (Def Real a) => Real (Lift Real s a) where
  toRational a = toRational_ REFLECT (lower a)

instance ReifiableConstraint Real where
 data Def Real a = Real
   { toRational_ :: a -> Rational
   , ordDef      :: Def Ord a
   , numDef      :: Def Num a
   }
 reifiedIns = Sub Dict

{-
instance Reifies s (Def Integral a) => Real (Lift Integral s a) where
   toRational a = (toRational_ $ realDef REFLECT) (lower a)

instance Reifies s (Def Integral a) => Integral (Lift Integral s a) where
   quot    a b = Lift $ quot_    REFLECT (lower a) (lower b)
   rem     a b = Lift $ rem_     REFLECT (lower a) (lower b)
   div     a b = Lift $ div_     REFLECT (lower a) (lower b)
   mod     a b = Lift $ mod_     REFLECT (lower a) (lower b)
   quotRem a b = over both Lift $ quotRem_ REFLECT (lower a) (lower b)
   divMod  a b = over both Lift $ divMod_  REFLECT (lower a) (lower b)
   toInteger a = toInteger_ REFLECT (lower a)

instance ReifiableConstraint Integral where
  data Def Integral a = Integral
     { quot_      :: a -> a -> a
     , rem_       :: a -> a -> a
     , div_       :: a -> a -> a
     , mod_       :: a -> a -> a
     , quotRem_   :: a -> a -> (a, a)
     , divMod_    :: a -> a -> (a, a)
     , toInteger_ :: a -> Integer
     , realDef    :: Def Real a
     }
  reifiedIns = Sub Dict

instance Reifies s (Def Fractional a) => Fractional (Lift Fractional s a) where
  (/)          a b = Lift $ (/.) REFLECT (lower a) (lower b)
  recip        a b = Lift $ recip REFLECT (lower a) (lower b)
  fromRational a b = Lift $ fromRational_ REFLECT (lower a) (lower b)

instance ReifiableConstraint Fractional where
  data Def Fractional a = Fractional
      { (/.)          :: a -> a -> a
      , recip_        :: a -> a
      , fromRational_ :: Rational -> a
      }
  reifiedIns = Sub Dict

instance Reifies s (Def Floating a) => Floating (Lift Floating s a) where
   pi          = Lift $ pi_      reflect (Proxy :: Proxy s)
   exp     a   = Lift $ exp_     REFLECT (lower a)
   sqrt    a   = Lift $ sqrt_    REFLECT (lower a)
   log     a   = Lift $ log_     REFLECT (lower a)
   (**)    a b = Lift $ (**.)    REFLECT (lower a) (lower b)
   logBase a b = Lift $ logBase_ REFLECT (lower a) (lower b)
   sin     a   = Lift $ sin_     REFLECT (lower a)
   tan     a   = Lift $ tan_     REFLECT (lower a)
   cos     a   = Lift $ cos_     REFLECT (lower a)
   asin    a   = Lift $ asin_    REFLECT (lower a)
   atan    a   = Lift $ atan_    REFLECT (lower a)
   acos    a   = Lift $ acos_    REFLECT (lower a)
   sinh    a   = Lift $ sinh_    REFLECT (lower a)
   tanh    a   = Lift $ tanh_    REFLECT (lower a)
   cosh    a   = Lift $ cosh_    REFLECT (lower a)
   asinh   a   = Lift $ asinh_   REFLECT (lower a)
   atanh   a   = Lift $ atanh_   REFLECT (lower a)
   acosh   a   = Lift $ acosh_   REFLECT (lower a)

instance ReifiableConstraint Floating where
  data Def Floating a = Floating
      { pi_      :: a
      , exp_     :: a -> a
      , sqrt_    :: a -> a
      , log_     :: a -> a
      , (**.)    :: a -> a -> a
      , logBase_ :: a -> a -> a
      , sin_     :: a -> a
      , tan_     :: a -> a
      , cos_     :: a -> a
      , asin_    :: a -> a
      , atan_    :: a -> a
      , acos_    :: a -> a
      , sinh_    :: a -> a
      , tanh_    :: a -> a
      , cosh_    :: a -> a
      , asinh_   :: a -> a
      , atanh_   :: a -> a
      , acosh_   :: a -> a
      }
  reifiedIns = Sub Dict

instance Reifies s (Def RealFrac a) => RealFrac (Lift RealFrac s a) where
   properFraction a = fmap Lift $ properFraction_ REFLECT (lower a)
   truncate       a =      Lift $ truncate_       REFLECT (lower a)
   round          a =      Lift $ round_          REFLECT (lower a)
   ceiling        a =      Lift $ ceiling_        REFLECT (lower a)
   floor          a =      Lift $ floor_          REFLECT (lower a)


instance ReifiableConstraint RealFrac where
  data Def RealFrac a = RealFrac
      { properFraction_ :: Integral b => a -> (b, a)
      , truncate_       :: Integral b => a -> b
      , round_          :: Integral b => a -> b
      , ceiling_        :: Integral b => a -> b
      , floor_          :: Integral b => a -> b
      }
  reifiedIns = Sub Dict

instance Reifies s (Def RealFloat a) => RealFloat (Lift RealFloat s a) where
   floatRadix     a   = floatRadix_     REFLECT (lower a)
   floatDigits    a   = floatDigits_    REFLECT (lower a)
   floatRange     a   = floatRange_     REFLECT (lower a)
   decodeFloat    a   = decodeFloat_    REFLECT (lower a)
   encodeFloat    a b = encodeFloat_    (reflect b) (lower a) (lower b)
   exponent       a   = exponent_       REFLECT (lower a)
   significand    a b = significand_    (reflect b) (lower a) (lower b)
   scaleFloat     a b = scaleFloat_     (reflect b) (lower a) (lower b)
   isInfinite     a   = isInfinite_     REFLECT (lower a)
   isDenormalized a   = isDenormalized_ REFLECT (lower a)
   isNegativeZero a   = isNegativeZero_ REFLECT (lower a)
   isIEEE         a   = isIEEE_         REFLECT (lower a)
   atan2          a   = atan2_          REFLECT (lower a)

instance ReifiableConstraint RealFloat where
  data Def RealFloat a = RealFloat
      { floatRadix_  :: a -> Integer
      , floatDigits_ :: a -> Int
      , floatRange_  :: a -> (Int, Int)
      , decodeFloat_ :: a -> (Integer, Int)
      , encodeFloat_ :: Integer -> Int -> a
      , exponent_    :: a -> Int
      , significand_  :: Int -> a -> a
      , scaleFloat_   :: Int -> a -> a
      , isInfinite_   :: a -> Bool
      , isDenormalized_ :: a -> Bool
      , isNegativeZero_ :: a -> Bool
      , isIEEE_         :: a -> Bool
      , atan2_          :: a -> Bool
      }
  reifiedIns = Sub Dict
-}

{-
I think this will need a reifyable constraint1
instance Reifies s (Def Monad a) => Monad (Lift Monad s a) where
   (>>=)  =
   (>>)   =
   return =
   fail   =

instance ReifiableConstraint Monad where
  data Def Monad a = Monad
      { (>>=.) :: forall a b. m a -> (a -> m b) -> m b
      , (>>.)  :: forall a b. m a -> m b -> m b
      , return :: a -> m a
      , fail   :: String -> m a
      }
  reifiedIns = Sub Dict
-}

instance Reifies s (Def Show a) => Show (Lift Show s a) where
  show = show_ REFLECT . lower

instance ReifiableConstraint Show where
  data Def Show a = Show { show_ :: a -> String }
  reifiedIns = Sub Dict

instance ReifiableConstraint Read where
  data Def Read a = Read { readsPrec_ :: Int -> ReadS a, readList_ :: ReadS [a] }
  reifiedIns = Sub Dict

instance Reifies s (Def Read a) => Read (Lift Read s a) where
  readsPrec x s = over _1 Lift <$> readsPrec_ REFLECT x s
  readList  s   = over _1 (fmap Lift)
               <$> readList_  REFLECT s

instance ReifiableConstraint Eq where
  data Def Eq a = Eq { eq_ :: a -> a -> Bool }
  reifiedIns = Sub Dict

instance Reifies s (Def Eq a) => Eq (Lift Eq s a) where
   x == y = eq_ REFLECT (lower x) (lower y)

instance ReifiableConstraint Ord where
  data Def Ord a = Ord { compare_ :: a -> a -> Ordering }
  reifiedIns = Sub Dict

instance Reifies s (Def Ord a) => Eq (Lift Ord s a) where
  a == b = compare a b == EQ

instance Reifies s (Def Ord a) => Ord (Lift Ord s a) where
  compare a b = compare_ REFLECT (lower a) (lower b)

instance ReifiableConstraint Monoid where
  data Def Monoid a = Monoid { mappend_ :: a -> a -> a, mempty_ :: a }
  reifiedIns = Sub Dict

instance Reifies s (Def Monoid a) => Monoid (Lift Monoid s a) where
  mappend = liftA2 (mappend_ REFLECT)
  mempty  = pure $ mempty_ REFLECT

-- Aeson Instances
instance ReifiableConstraint FromJSON where
   data Def FromJSON a = FromJSON { parseJSON_ :: Value -> Parser a }
   reifiedIns = Sub Dict

instance Reifies s (Def FromJSON a) => FromJSON (Lift FromJSON s a) where
   parseJSON = fmap pure . parseJSON_ REFLECT

instance ReifiableConstraint ToJSON where
   data Def ToJSON a = ToJSON { toJSON_ :: a -> Value}
   reifiedIns = Sub Dict

instance Reifies s (Def ToJSON a) => ToJSON (Lift ToJSON s a) where
   toJSON a = toJSON_ REFLECT (lower a)
