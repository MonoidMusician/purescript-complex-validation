module Complex.Validation where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Monad.Writer as W
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Const (Const(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Variant (SProxy)
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.Symbol (class IsSymbol)
import Data.These (These(..))
import Data.Tuple (Tuple(..))
import Data.Variant as V

-- | A recursive variant thingy.
type MuV r = Mu (VF.VariantF r)
-- | An extensible error using `Variant`.
type Errors es = Erroring (V.Variant es)
-- | Extensible errors with `Mu (VariantF ...)`, giving access to *R*ecursion.
-- | This is useful for errors that carry context, like a call stack or trace.
type ERrors es = Erroring (MuV es)
-- | An extensible warning using `Variant`.
type Warnings ws = W.WriterT (Array (V.Variant ws))
type WaRnings ws = W.WriterT (Array (MuV ws))
-- | Warnings put together with errors
type Feedback ws es = Warnings ws (Errors es)
-- | Recursive warnings and errors.
type FeedbackR ws es = WaRnings ws (ERrors es)

-- | Yet another alternative validation type, this one uses two layers of
-- | NonEmptyArray instead of a generic/free Semiring, in order to guarantee
-- | that an error is actually thrown. Thus it does not provide `empty`; you
-- | must supply your own error for a failure case.
data Erroring e a
  = Success a
  | Error (NEA.NonEmptyArray (NEA.NonEmptyArray e))

derive instance eqErroring :: (Eq e, Eq a) => Eq (Erroring e a)

instance showErroring :: (Show e, Show a) => Show (Erroring e a) where
  show (Success a) = "(Success " <> show a <> ")"
  show (Error es) = "(Error " <> show es <> ")"

instance functorErroring :: Functor (Erroring e) where
  map f (Success a) = Success (f a)
  map _ (Error e) = Error e

instance bifunctorErroring :: Bifunctor Erroring where
  bimap _ g (Success a) = Success (g a)
  bimap f _ (Error e) = Error (map (map f) e)

instance applyErroring :: Apply (Erroring e) where
  apply (Success f) (Success a) = Success (f a)
  apply (Error es) (Success _) = Error es
  apply (Success _) (Error es) = Error es
  apply (Error e1s) (Error e2s) = Error ((<|>) <$> e1s <*> e2s)

instance applicativeErroring :: Applicative (Erroring e) where
  pure = Success

instance altErroring :: Alt (Erroring e) where
  alt a b = altThese a b <#> leftBias

instance bindErroring :: Bind (Erroring e) where
  bind (Success a) f = f a
  bind (Error es) _ = Error es

-- | This is like `alt` but it returns the successes with `These`, so it
-- | does not have a left or right bias.
altThese :: forall a b e. Erroring e a -> Erroring e b -> Erroring e (These a b)
altThese (Success a) (Success b) = Success (Both a b)
altThese (Success a) (Error _) = Success (This a)
altThese (Error _) (Success b) = Success (That b)
altThese (Error e1s) (Error e2s) = Error (e1s <|> e2s)

-- | Helper to squash `These`.
leftBias :: forall a. These a a -> a
leftBias (Both a _) = a
leftBias (This a) = a
leftBias (That a) = a

--------------------------------------------------------------------------------

-- | Throw an error! No frills.
erroring :: forall e a. e -> Erroring e a
erroring = Error <<< pure <<< pure

-- | Throw an extensible error with `Variant`.
error ::
  forall s t r' r a.
    RowCons s t r' r =>
    IsSymbol s =>
  SProxy s -> t -> Errors r a
error s = erroring <<< V.inj s

-- | Throw an error with `Mu (VariantF ...)`.
errorR ::
  forall s f r' r a.
    RowCons s (VF.FProxy f) r' r =>
    Functor f =>
    IsSymbol s =>
  SProxy s -> f (MuV r) -> ERrors r a
errorR s = erroring <<< In <<< VF.inj s

-- | Throw a simple (non-recursive) error (in a context that allows recursion).
errorSimple ::
  forall s t r' r a.
    RowCons s (VF.FProxy (Const t)) r' r =>
    IsSymbol s =>
  SProxy s -> t -> ERrors r a
errorSimple s = errorR s <<< Const

-- | Scope an error-ful computation, meaning that any error emitted in the
-- | inner computation is rethrown with more context in the outer computation.
-- | Extra information about the context is carried in the `t` type.
errorScoped ::
  forall s t r' r a.
    RowCons s (VF.FProxy (Tuple t)) r' r =>
    IsSymbol s =>
  SProxy s -> t -> ERrors r a -> ERrors r a
errorScoped s t = lmap (In <<< VF.inj s <<< Tuple t)

-- | Scope a computation with no extra data in the scope, besides its label.
errorScopedSimple ::
  forall s r' r.
    RowCons s (VF.FProxy Identity) r' r =>
    IsSymbol s =>
  SProxy s -> ERrors r ~> ERrors r
errorScopedSimple s = lmap (In <<< VF.inj s <<< Identity)

--------------------------------------------------------------------------------

-- | Emite a warning! No frills.
warning :: forall w m. Applicative m => w -> W.WriterT w m Unit
warning = W.WriterT <<< pure <<< Tuple unit

-- | Emit an extensible warning with `Variant`.
warn ::
  forall s t r' r m.
    Applicative m =>
    RowCons s t r' r =>
    IsSymbol s =>
  SProxy s -> t -> Warnings r m Unit
warn s = warning <<< pure <<< V.inj s

-- | Emit a warning with `Mu (VariantF ...)`.
warnR ::
  forall s f r' r m.
    Applicative m =>
    RowCons s (VF.FProxy f) r' r =>
    Functor f =>
    IsSymbol s =>
  SProxy s -> f (MuV r) -> WaRnings r m Unit
warnR s = warning <<< pure <<< In <<< VF.inj s

-- | Emit a simple (non-recursive) warning (in a context that allows recursion).
warnSimple ::
  forall s t r' r m.
    Applicative m =>
    RowCons s (VF.FProxy (Const t)) r' r =>
    IsSymbol s =>
  SProxy s -> t -> WaRnings r m Unit
warnSimple s = warnR s <<< Const

-- | Scope a warning.
warnScoped ::
  forall s t r' r m.
    Functor m =>
    RowCons s (VF.FProxy (Tuple t)) r' r =>
    IsSymbol s =>
  SProxy s -> t -> WaRnings r m ~> WaRnings r m
warnScoped s t = W.mapWriterT $ map $ map $ map $
  In <<< VF.inj s <<< Tuple t

-- | Scope a warning with no extra context.
warnScopedSimple ::
  forall s r' r m.
    Functor m =>
    RowCons s (VF.FProxy Identity) r' r =>
    IsSymbol s =>
  SProxy s -> WaRnings r m ~> WaRnings r m
warnScopedSimple s = W.mapWriterT $ map $ map $ map $
  In <<< VF.inj s <<< Identity

--------------------------------------------------------------------------------

-- | Lift from Errors to Feedback, ERrors to FeedbackR
lift :: forall f a m. Functor f => Monoid m => f a -> W.WriterT m f a
lift m = W.WriterT (Tuple <$> m <@> mempty)

-- | Scope both errors and warnings.
scoped ::
  forall s t es' es ws' ws.
    RowCons s (VF.FProxy (Tuple t)) es' es =>
    RowCons s (VF.FProxy (Tuple t)) ws' ws =>
    IsSymbol s =>
  SProxy s -> t -> FeedbackR ws es ~> FeedbackR ws es
scoped s t = warnScoped s t <<< W.mapWriterT (errorScoped s t)

scopedSimple ::
  forall s es' es ws' ws.
    RowCons s (VF.FProxy Identity) es' es =>
    RowCons s (VF.FProxy Identity) ws' ws =>
    IsSymbol s =>
  SProxy s -> FeedbackR ws es ~> FeedbackR ws es
scopedSimple s = warnScopedSimple s <<< W.mapWriterT (errorScopedSimple s)

-- | Any warnings thrown become errors.
escalate :: forall e. W.WriterT (Array e) (Erroring e) ~> Erroring e
escalate (W.WriterT (Error es)) = Error es
escalate (W.WriterT (Success (Tuple a ws))) =
  case NEA.fromArray ws of
    Just es -> Error $ pure <$> es
    Nothing -> Success a

-- | What do you call escalating without proof that it worked?
sisyphus :: forall e. W.WriterT (Array e) (Erroring e) ~> W.WriterT (Array e) (Erroring e)
sisyphus = lift <<< escalate