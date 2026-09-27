module Unify where

import Data.Map (Map)
import Data.Set (Set)

deriving instance (Show a, Show (Var a)) => Show (Scheme a)
deriving instance                 Show a => Show (Constraint a)

type family Var a
type family Val a                = r | r -> a

type Constraints a               = [Constraint (Val a)]
data Constraint a                = Constraint a a
type Context a                   = [Scheme a]
data Scheme a                    = Scheme (Set (Var a)) a
type Subst a                     = Map (Var a) (Val a)
