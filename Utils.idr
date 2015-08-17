module Utils

import Data.Fin
import Data.Vect

-- Serial composition (quite useful)
infixr 8 ^
(^) : (a -> a) -> Nat -> (a -> a)
(^) f Z = id
(^) f (S k) = (f^k) . f
