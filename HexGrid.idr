module HexGrid

import Data.Fin
import Data.Vect

------------------
-- HexDirection --
------------------

data HexDirection = A | B | C | D | E | F 

rotate : HexDirection -> HexDirection
rotate A = B
rotate B = C
rotate C = D
rotate D = E
rotate E = F
rotate F = A

spin : Nat -> HexDirection -> HexDirection
spin Z x = x
spin (S k) x = spin k (rotate x)

invert : HexDirection -> HexDirection
invert x = spin 3 x

instance Enum HexDirection where
  pred x = spin 5 x

  succ x = rotate x

  toNat A = 4
  toNat B = 5
  toNat C = 0
  toNat D = 1
  toNat E = 2
  toNat F = 3

  fromNat n = spin n C

instance Eq HexDirection where
  (==) A A = True
  (==) A _ = False
  (==) B B = True
  (==) B _ = False
  (==) C C = True
  (==) C _ = False
  (==) D D = True
  (==) D _ = False
  (==) E E = True
  (==) E _ = False
  (==) F F = True
  (==) F _ = False

-- TODO: Implement proper ordering
instance Ord HexDirection where
  compare e1 e2 = compare (toNat e1) (toNat e2)

------------
-- HexPos --
------------

-- A position is either :
-- - the Origin (the position of the center tile), or
-- - a combination (Pos) of :
--      * the position of the 'ring' (0 or 1 ; more for a bigger board)
--      * the 'edge', also the direction of the branch
--        it's the direction you need to take to access the next tile
--      * the position of the 'tile', which is the index on the edge ;
--        it goes from 0 to the index of the current ring
-- So the board is both a spiral of tiles
-- and a polar grid of 6 axes
data HexPos : Type where
  Origin : HexPos
  Pos : (r:Nat) -> HexDirection -> (Fin (S r)) -> HexPos

instance Enum HexPos where
  pred Origin = Origin
  pred (Pos Z C FZ) = Origin
  pred (Pos (S pr) C FZ) = Pos pr B last 
  pred (Pos r e FZ) = Pos r (spin 5 e) last
  pred (Pos r e (FS pt)) = Pos r e (weaken pt)

  succ Origin = Pos Z C FZ
  succ (Pos r B t) = either fLast fNotLast (strengthen (shift 1 t)) where
    fLast x = Pos (S r) C FZ
    fNotLast x = Pos r B x
  succ (Pos r e t) = either fLast fNotLast (strengthen (shift 1 t)) where
    fLast x = Pos r (rotate e) FZ
    fNotLast x = Pos r e x

  toNat Origin = Z
  toNat (Pos r e t) = nrings r + (toNat e)*(S r) + (finToNat t) where
    nrings Z = 1
    nrings (S k) = 6*(S k) + nrings k

  fromNat Z = Origin
  fromNat (S k) = succ (fromNat k)

instance Eq HexPos where
  (==) Origin Origin = True
  (==) Origin _ = False
  (==) (Pos _ _ _) Origin = False
  (==) (Pos r1 e1 t1) (Pos r2 e2 t2) = if r1 /= r2
                                       then False
                                       else if e1 /= e2
                                            then False
                                            else toNat t1 == toNat t2

-- TODO: Implement proper ordering
instance Ord HexPos where
  compare Origin Origin = EQ
  compare Origin _ = LT
  compare (Pos _ _ _) Origin = GT
  compare hp1 hp2 = compare (toNat hp1) (toNat hp2)

diff : HexPos -> HexPos -> Nat
diff x Origin = toNat x
diff x y = diff (pred x) (pred y)

add : Nat -> HexPos -> HexPos
add Z p = p
add (S k) p = succ (add k p)

--------------
-- HexChain --
--------------

-- A HexChain is a list of elements
-- where you know the position of the first element
-- and the one who should come after the chain

data HexChain : HexPos -> HexPos -> Type -> Type where
  Nil : HexChain end end a
  (::) : a -> HexChain end beg a -> HexChain (succ end) beg a

-- Append two chains (transitivity verified without effort, so cool! )
(++) : HexChain end mid a -> HexChain mid beg a -> HexChain end beg a
(++) Nil ys = ys
(++) (x::xs) ys = x::(xs ++ ys)

-- For now no type inference, meaning when using rep
-- you must supply both the end position and the number of repetitions
-- Could be solved by asking for the end position instead? Maybe...
rep : (n : Nat) -> (p : HexPos) -> a -> HexChain (add n p) p a
rep Z _ _ = Nil
rep (S k) p x = x::(rep k p x)

updateAt' : (n : Nat) -> (f : a -> a) -> HexChain end beg a -> HexChain end beg a
updateAt' Z f hc = hc 
updateAt' (S k) f Nil = Nil
updateAt' (S Z) f (x::xs) = (f x)::xs
updateAt' (S (S k)) f (x::xs) = x::(updateAt' (S k) f xs)

updateAt : (p : HexPos) -> (f : a -> a) -> HexChain end beg a -> HexChain end beg a
updateAt {end=end} p f hc = updateAt' (diff end p) f hc

-------------
-- HexGrid --
-------------

-- A HexGrid is just a chain that
-- starts at the Origin and
-- has only completed rings
-- n gives the number of rings
HexGrid : Nat -> Type -> Type
HexGrid n a = HexChain (Pos n C FZ) Origin a 

