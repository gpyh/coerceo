module Utils

import Data.Fin
import Data.Vect

-- Serial composition (quite useful)
-- Beware of the order!
infixr 8 ^
(^) : (a -> a) -> Nat -> (a -> a)
(^) f Z = id
(^) f (S k) = f . (f^k)

-- TODO: Code this for a perfect 'succ' of HexPos
-- Tries to increment a Fin
-- If it can't, returns the same value
-- flow : Fin (S r) -> Fin (S r)
-- flow FZ = FS FZ
