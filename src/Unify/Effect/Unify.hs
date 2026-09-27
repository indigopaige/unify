module Unify.Effect.Unify
  ( Substitutable(..)
  , UnifyError(..)
  , Constraint(..)
  , Unifiable(..)
  , instantiate
  , generalize
  , Scheme(..)
  , runUnify
  , Unify
  , Subst
  , (<=>)
  , (<.>)
  , fresh
  , Var
  , Val
  , mgu
  )
where

import Effectful.Writer.Static.Local
import Effectful.Dispatch.Dynamic
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Error.Static

import Data.Map (Map)
import Data.Set (Set)
import Effectful.TH
import GHC.Generics
import Effectful
import Unify

import Unify.Effect.Counter

class Ord (Var a) => Substitutable a b | b -> a where
  (.$) :: Subst a -> b -> b
  vars :: b -> Set (Var a)

instance Substitutable a b => Substitutable a (Constraint b) where
  vars (Constraint t t') = vars t `Set.union` vars t'
  s .$ Constraint t t'   = Constraint (s .$ t) (s .$ t')

instance Substitutable a a => Substitutable a (Scheme a) where
  vars (Scheme bound t) = vars t `Set.difference` bound
  s .$ Scheme bound t   = Scheme bound $ s' .$ t
    where
      s' = foldr Map.delete s bound

instance Substitutable a b => Substitutable a [b] where
  vars    = foldr (Set.union . vars) mempty
  s .$ xs = fmap (s .$) xs

class ( Substitutable a a
      , Substitutable a (Val a)
      , Generic (Val a)
      , GMatches (Val a) (Rep (Val a))
      , Enum idx
      ) => Unifiable a idx | idx -> a
                           , a -> idx where
  fromIdx :: idx -> Val a
  getVar  :: Val a -> Maybe (Var a)

newtype Ignore a = Ignore a
  deriving ( Show
           , Ord
           , Eq
           )

class MatchField v a where
  matchField :: a -> a -> Maybe [(v, v)]

instance MatchField v v where
  matchField x y = Just [(x, y)]

instance MatchField v (Ignore a) where
  matchField _ _ = Just []

instance MatchField v a => MatchField v [a] where
  matchField [] []         = Just []
  matchField (x : xs) (y : ys) =
    (<>) <$> matchField @v x y
         <*> matchField @v xs ys
  matchField _ _           = Nothing

instance {-# OVERLAPPABLE #-} Eq a => MatchField v a where
  matchField x y
    | x == y    = Just []
    | otherwise = Nothing

class GMatches v f where
  gmatches :: f p
           -> f p
           -> Maybe [(v, v)]

instance (GMatches v f, GMatches v g)
      => GMatches v (f :+: g) where
  gmatches (L1 x) (L1 y) = gmatches @v x y
  gmatches (R1 x) (R1 y) = gmatches @v x y
  gmatches _      _      = Nothing

instance GMatches v f
      => GMatches v (M1 i c f) where
  gmatches (M1 x) (M1 y) = gmatches @v x y

instance (GMatches v f, GMatches v g)
      => GMatches v (f :*: g) where
  gmatches (x :*: y) (x' :*: y') =
    (<>) <$> gmatches @v x x'
         <*> gmatches @v y y'

instance MatchField v a => GMatches v (K1 i a) where
  gmatches (K1 x) (K1 y) =
    matchField @v x y

instance GMatches v U1 where
  gmatches U1 U1 = Just []

matches :: forall a idx.
           Unifiable a idx
        => Val a
        -> Val a
        -> Maybe [(Val a, Val a)]

matches x y = gmatches @(Val a) (from x) (from y)

data Unify a idx :: Effect where
  Unify :: Unifiable a idx
        => Val a
        -> Val a
        -> Unify a idx m ()

  Fresh :: Unifiable a idx
        => Unify a idx m (Val a)


makeEffect ''Unify

(<=>) :: (Unify a idx :> es , Unifiable a idx)
      => Val a
      -> Val a
      -> Eff es ()

(<=>) = unify

infixr 8 <=>

(<.>) :: forall a. Substitutable a (Val a)
      => Subst a
      -> Subst a
      -> Subst a

s1 <.> s2 = Map.map (s1 .$) s2 `Map.union` s1

infixr 8 <.>

instantiate :: forall a idx es.
               ( Unifiable a idx
               , Unify a idx :> es
               )
            => Scheme a
            -> Eff es a

instantiate (Scheme bound t) = do
  let n = Set.toList bound
  r <- traverse (const fresh) n
  let s = Map.fromList $ zip n r
  pure $ s .$ t

generalize :: Substitutable a a
           => Context a
           -> a
           -> Scheme a

generalize ctx t = Scheme (vars t `Set.difference` vars ctx) t

data UnifyError a
  = Infinite (Var a) (Val a)
  | Mismatch (Val a) (Val a)

deriving instance (Show (Var a), Show (Val a)) => Show (UnifyError a)

bind :: forall a idx es.
        ( Error (UnifyError a) :> es
        , Unifiable a idx
        )
     => Var a
     -> Val a
     -> Eff es (Subst a)

bind v t
  | Just v == getVar t      = pure mempty
  | v `Set.member` vars t   = throwError_ $ Infinite v t
  | otherwise               = pure $ Map.singleton v t

unify' :: forall a idx es.
          ( Error (UnifyError a) :> es
          , Unifiable a idx
          )
       => Val a
       -> Val a
       -> Eff es (Subst a)
unify' v t | Just v' <- getVar v = bind v' t
unify' v t | Just t' <- getVar t = bind t' v

unify' v t = case matches v t of
               Nothing -> throwError_ $ Mismatch v t
               Just x  -> unifyMany x

unifyMany :: forall a idx es.
             ( Error (UnifyError a) :> es
             , Unifiable a idx
             )
          => [(Val a, Val a)]
          -> Eff es (Subst a)

unifyMany []             = pure mempty
unifyMany ((t, t') : ts) = do
  s <- unify' t t'
  let ts' = fmap (\(x, y) ->
                      ( s .$ x
                      , s .$ y
                      )) ts

  s' <- unifyMany ts'
  pure $ s' <.> s

solve :: forall a idx es.
         ( Error (UnifyError a) :> es
         , Unifiable a idx
         )
      => Subst a
      -> Constraints a
      -> Eff es (Subst a)

solve s []                     = pure s
solve s (Constraint t t' : cs) = do
  s' <- unify' (s .$ t) (s .$ t')
  solve (s' <.> s) cs

mgu :: forall a idx es.
       ( Error (UnifyError a) :> es
       , Unifiable a idx
       )
    => Val a
    -> Val a
    -> Eff es (Subst a)

mgu = unify' @a @idx

runUnify :: forall a idx es.
            ( Error (UnifyError a) :> es
            , Unifiable a idx
            )
         => Eff (Unify a idx : es) a
         -> Eff es a

runUnify a = do
  (r, cs) <- handle a
  s <- solve @a @idx mempty cs
  pure $ s .$ r
 where
    handle =
      reinterpret runner $ \_ -> \case
        Unify x y -> tell [Constraint x y]
        Fresh     -> fromIdx . toEnum <$> freshInt

    runner = runCounter
           . runWriter @(Constraints a)
