module HexGrid

import Data.Fin
import Utils

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

-- Allows to express the position on a HexChain as either :
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
  
  -- Not the most optimized code (there's a useless call to succ)
  -- Totality checker doesn't like it either
  -- BUT there's no need to check for the bound of t
  succ Origin = Pos Z C FZ
  succ (Pos Z B FZ) = Pos (S Z) C FZ
  succ (Pos Z e t) = Pos Z (succ e) t
  succ (Pos (S r) e FZ) = Pos (S r) e (FS FZ) 
  succ (Pos (S r) e (FS t)) with (assert_total (succ (Pos r e t)))
    | Pos sr se FZ = Pos (S sr) se FZ
    | Pos sr _ st = Pos (S sr) e (FS st)
    | Origin = Origin -- Just so the totality checker doesn't freak out

  toNat Origin = Z
  toNat (Pos r e t) = nrings r + (toNat e)*(S r) + (finToNat t) where
    nrings Z = 1
    nrings (S k) = 6*(S k) + nrings k
  
  fromNat n = (succ^n) Origin

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
-- where you know the position of the first element on a hypothetical
-- hexagonal grid (HexGrid) and the position of the last tile if you
-- added one (the possition of the 'following' tile)

data HexChain : HexPos -> HexPos -> Type -> Type where
  Nil : HexChain beg beg a
  (::) : a -> HexChain end beg a -> HexChain (succ end) beg  a

instance Functor (HexChain end beg) where
  map m Nil = Nil
  map m (x :: xs) = m x :: map m xs

instance Foldable (HexChain end beg) where
  foldr f e hc = foldr' f e id hc where
    foldr' : (a -> acc -> acc) -> acc -> (acc -> acc) ->
             HexChain end beg a -> acc
    foldr' f e go Nil = go e
    foldr' f e go (x :: xs) = foldr' f e (go . (f x)) xs

instance Traversable (HexChain end beg) where
  traverse f Nil = pure Nil
  traverse f (x :: xs) = [| f x :: traverse f xs |]

-- Append two chains 
-- Transitiviy is free! :D
(++) : HexChain end mid a -> HexChain mid beg a -> HexChain end beg a
(++) Nil ys = ys
(++) (x::xs) ys = x::(xs ++ ys)

replicate : (n : Nat) -> a -> HexChain ((succ^n) beg) beg a
replicate Z _ = Nil 
replicate (S k) x = x :: replicate k x

endPos : HexChain end beg a -> HexPos
endPos {end} hc = end 

updateAt : (p : HexPos) -> (f : a -> a) ->
           HexChain end beg a -> HexChain end beg a
updateAt p f Nil = Nil
updateAt p f (x::xs) = if p == endPos xs
                       then (f x)::xs
                       else x::(updateAt p f xs)

-- Alternative update fuction so it can handle the Maybe's
-- That's just temporary though, until I find a better way to
-- manage exceptions (and I learn how to better do the monadic black magic)
mUpdateAt : (Alternative app) => (p : HexPos) -> (f : a -> app a) ->
      HexChain end beg a -> app (HexChain end beg a)
mUpdateAt p f Nil = empty
mUpdateAt p f (x::xs) = if p == endPos xs
                       then liftA2 (::) (f x) (pure xs)
                       else liftA2 (::) (pure x) (mUpdateAt p f xs)
-------------
-- HexGrid --
-------------

-- A HexGrid is just a chain that
-- starts at the Origin and
-- has only completed rings
-- n gives the number of rings
HexGrid : Nat -> Type -> Type
HexGrid n a = HexChain (Pos n C FZ) Origin a 

