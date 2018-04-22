module Test.Complex.Validation where

import Prelude

import Complex.Validation (Erroring(..), erroring)
import Control.Alt (class Alt, (<|>))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Control.Monad.Gen (choose)
import Data.Bifunctor (class Bifunctor)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Test.QuickCheck (class Arbitrary, (===))
import Test.QuickCheck as QC
import Test.QuickCheck.Gen (resize)
import Test.QuickCheck.Laws.Control as QCLC
import Type.Proxy (Proxy2(..))

newtype Wrapped e a = Wrapped (Erroring e a)
derive instance newtypeWrapped :: Newtype (Wrapped e a) _
derive newtype instance eqWrapped :: (Eq e, Eq a) => Eq (Wrapped e a)
derive newtype instance functorWrapped :: Functor (Wrapped e)
derive newtype instance bifunctorWrapped :: Bifunctor Wrapped
derive newtype instance applyWrapped :: Apply (Wrapped e)
derive newtype instance applicativeWrapped :: Applicative (Wrapped e)
derive newtype instance bindWrapped :: Bind (Wrapped e)
derive newtype instance altWrapped :: Alt (Wrapped e)

instance showWrapped :: (Show e, Show a) => Show (Wrapped e a) where
  show (Wrapped (Success a)) = "(Success " <> show a <> ")"
  show (Wrapped (Error es)) = "(Error " <> show es <> ")"

instance arbitraryWrapped :: (Arbitrary e, Arbitrary a) =>
  Arbitrary (Wrapped e a) where
    arbitrary = Wrapped <$> choose
      (Error <$> resize 3 QC.arbitrary)
      (Success <$> QC.arbitrary)


main :: forall e. Eff ( console :: CONSOLE, exception :: EXCEPTION, random :: RANDOM | e ) Unit
main = do
  let logShowWrapped = logShow <<< Wrapped :: Erroring Int Unit -> Wrapped Int Unit
  logShowWrapped $ erroring 1 <|> erroring 2
  logShowWrapped $ erroring 1 <|> erroring 2 <|> erroring 3
  logShowWrapped $ (erroring 1 <|> erroring 2) <*> erroring 3
  logShowWrapped $ (erroring 1 <*> erroring 3) <|> (erroring 2 <*> erroring 3)
  QCLC.checkApply (Proxy2 :: Proxy2 (Wrapped Int))
  QCLC.checkApplicative (Proxy2 :: Proxy2 (Wrapped Int))
  QCLC.checkBind (Proxy2 :: Proxy2 (Wrapped Int))
  QCLC.checkAlt (Proxy2 :: Proxy2 (Wrapped Int))
  log "Check other alternative instances:"
  log "Array:" *> QCLC.checkAlternative (Proxy2 :: Proxy2 Array)
  log "Maybe:" *> QCLC.checkAlternative (Proxy2 :: Proxy2 Maybe)

  -- Not sure if this is supposed to hold or not, who knows.
  log "Checking 'Distributivity' law for pseudo-Alternative"
  let
    distributivity :: Wrapped Int (Ordering -> Ordering) -> Wrapped Int (Ordering -> Ordering) -> Wrapped Int Ordering -> QC.Result
    distributivity f g x = ((f <|> g) <*> x) === ((f <*> x) <|> (g <*> x))
  QC.quickCheck' 1000 distributivity
