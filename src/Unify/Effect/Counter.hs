module Unify.Effect.Counter where

import Effectful.Dispatch.Static
import Effectful

data Counter :: Effect

type    instance DispatchOf Counter = Static NoSideEffects
newtype instance StaticRep  Counter = Counter Word

freshWord :: Counter :> es => Eff es Word
freshWord = do
  Counter count <- getStaticRep
  putStaticRep $ Counter (count + 1)
  pure count

freshInt :: Counter :> es => Eff es Int
freshInt = fromIntegral <$> freshWord

runCounter :: Eff (Counter : es) a -> Eff es a
runCounter = evalStaticRep (Counter 0)
