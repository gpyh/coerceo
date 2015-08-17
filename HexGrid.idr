module HexGrid

import Data.Fin
import Data.Vect

-----------
-- Utils --
-----------

-- Serial composition (quite useful)
infixr 8 ^
(^) : (a -> a) -> Nat -> (a -> a)
(^) f Z = id
(^) f (S k) = (f^k) . f

------------------
-- HexDirection --
------------------

data HexDirection = A | B | C | D | E | F 

instance Enum HexDirection where
  succ A = B
  succ B = C
  succ C = D
  succ D = E
  succ E = F
  succ F = A

  pred x = (succ^5) x

  toNat A = 4
  toNat B = 5
  toNat C = 0
  toNat D = 1
  toNat E = 2
  toNat F = 3

  fromNat n = (succ^n) C

instance Eq HexDirection where
  (==) A A = True
  (==) B B = True
  (==) C C = True
  (==) D D = True
  (==) E E = True
  (==) F F = True
  (==) _ _ = False

-- TODO: Implement proper ordering
instance Ord HexDirection where
  compare e1 e2 = compare (toNat e1) (toNat e2)

------------
-- HexPos --
------------

-- Mainly used for views
-- Because it can be used for powerful mattern matching
-- Not sure though (I'm keeping it as a 'legacy')
-- And it can be useful for drawing 

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
  pred (Pos r e FZ) = Pos r ((succ^5)  e) last
  pred (Pos r e (FS pt)) = Pos r e (weaken pt)
  
  -- That function sucks in terms of complexity but could be
  -- useful to prove things related to pred (not sure though)
  succ Origin = Pos Z C FZ
  succ (Pos r B t) = (pred^r) (Pos (S r) C (weaken t))
  succ (Pos r e t) = (pred^r) (Pos r (succ e) t)

  toNat Origin = Z
  toNat (Pos r e t) = nrings r + (toNat e)*(S r) + (finToNat t) where
    nrings Z = 1
    nrings (S k) = 6*(S k) + nrings k

  fromNat n = (succ^n) Origin

hexPosFromNat : Nat -> HexPos
hexPosFromNat n = fromNat n

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
-- where you know the position of the first element on a hypothetical grid
-- and the one who should come after the chain on that same grid

data HexChain : Nat -> Nat -> Type -> Type where
  Nil : HexChain end end a
  (::) : a -> HexChain end beg a -> HexChain (succ end) beg a

-- Append two chains (transitivity verified without effort, so cool! )
(++) : HexChain end mid a -> HexChain mid beg a -> HexChain end beg a
(++) Nil ys = ys
(++) (x::xs) ys = x::(xs ++ ys)

replicate : (rep : Nat) -> a -> HexChain (beg+rep) beg a
replicate {beg=beg} rep x = rewrite sym (plusCommutative rep beg) in
                                     replicate' rep x where
                                       replicate' Z x = Nil
                                       replicate' (S k) x = x::(replicate' k x)

endPos : HexChain end beg a -> Nat
endPos {end=end} hc = end

updateAt : (p : Nat) -> (f : a -> a) -> HexChain end beg a -> HexChain end beg a
updateAt p f Nil = Nil
updateAt p f (x::xs) = if p == endPos xs
                       then (f x)::xs
                       else x::(updateAt p f xs)

-------------
-- HexGrid --
-------------

-- A HexGrid is just a chain that
-- starts at the Origin and
-- has only completed rings
-- n gives the number of rings
HexGrid : Nat -> Type -> Type
HexGrid n a = HexChain (toNat (Pos n C FZ)) Z a 

