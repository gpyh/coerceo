module Main

import HexGrid
import Utils
import Data.Fin
import Data.Vect

--------------------
-- Bunch of types --
--------------------

-- noNat


PiecePos : Type
PiecePos = HexDirection 

data FieldPos : Type where
  MkFieldPos : HexPos -> PiecePos -> FieldPos

data Color = White | Black

negate : Color -> Color
negate White = Black
negate Black = White

data Piece : Color -> Type where
  MkPiece : (color : Color) -> Piece color

data Player : Color -> Type where
  MkPlayer : (color : Color) -> Player color
  
data Tile : Type where
  NotOnB : (owner : Maybe (Player color)) -> Tile
  OnB : Vect 3 (Maybe (Piece White)) ->
        Vect 3 (Maybe (Piece Black)) -> Tile

Board : Type 
Board = HexGrid 2 Tile

--------------------
-- A little trick --
--------------------

-- The idea is to only define behavior for position C and D
-- Then, you just rotate the tile to end up with C and D
-- and rotate twice again after function application to land on your feet
-- This is cool, but FIXME.
-- This breaks totality so I should find a way to write the functions properly

shift : Vect 3 a -> Vect 3 a
shift (x :: y :: z :: Nil) = z :: x :: y :: Nil

-- rotates clockwise by 2
rotate : Tile -> Tile
rotate (OnB w b) = OnB (shift w) (shift b)
rotate t = t

--------------------
-- Starting board --
--------------------

-- Dangerous stuff!
-- Coercing into booleans is ill-advised!
-- That's fighting against the type system
-- It's used to make pairedTiles more elegant
-- I should do without: TODO
toTile : Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Tile
toTile c d e f a b =
  OnB (p c :: p e :: p a :: Nil) (p d :: p f :: p b :: Nil) where
     p : Bool -> Maybe (Piece color)
     p False = Nothing
     p True = Just (MkPiece color)

pairedTiles : (friendly : Bool) -> (posFstTile : PiecePos) -> Tile
pairedTiles fr C = toTile True False fr (not fr) False False
pairedTiles fr D = toTile False True False fr (not fr) False
pairedTiles fr e = rotate (pairedTiles fr ((succ^4) e))

emptyTile : Tile
emptyTile = OnB (nothing White) (nothing Black) where
  nothing : (color : Color) -> Vect 3 (Maybe (Piece color))
  nothing color = Nothing :: Nothing :: Nothing :: Nil

laurentius : Board
laurentius = lrt 18 where
  lrt : (n : Nat) -> HexChain ((succ^(S n)) beg) beg Tile
  lrt n with ((succ^n) Origin)
    lrt Z | Origin = emptyTile :: Nil 
    lrt (S k) | (Pos (S (S ppr)) _ _) = emptyTile :: lrt k
    lrt (S k) | (Pos r e t) = pairedTiles (t == FZ) (pred e) :: lrt k

-------------------
-- Moving Pieces --
-------------------

-- All the error handling is made with Maybe
-- TODO: Implement proper exceptions

pop : Vect n (Maybe a) -> Maybe (Vect n (Maybe a))
pop Nil = Nothing
pop (Nothing::xs) = Nothing 
pop (x::xs) = Just (Nothing::xs)

popPiece : PiecePos -> Tile -> Maybe Tile
popPiece _ (NotOnB _) = Nothing
popPiece C (OnB w b) = liftA2 OnB (pop w) (Just b)
popPiece D (OnB w b) = liftA2 OnB (Just w) (pop b)
popPiece e t = liftA (rotate^2) (popPiece ((succ^4) e) (rotate t))

push : a -> Vect n (Maybe a) -> Maybe (Vect n (Maybe a))
push _ Nil = Nothing
push y (Nothing::xs) = Just ((Just y)::xs)
push _ (x::xs) = Nothing

pushPiece : Piece color -> PiecePos -> Tile -> Maybe Tile
pushPiece _ _ (NotOnB _) = Nothing
pushPiece {color=White} p C (OnB w b) = liftA2 OnB (push p w) (Just b)
pushPiece {color=Black} p D (OnB w b) = liftA2 OnB (Just w) (push p b)
pushPiece p e t = liftA (rotate^2) (pushPiece p ((succ^4) e) (rotate t))
                       
-- (f : a -> m a) -> (g : a -> b -> b) -> b -> m b
-- (a -> b -> c) -> (m a -> m b -> m c)
-- liftA2 (::) (f x) xs

-- removePiece : Nat -> PiecePos -> Board -> Maybe Board
-- removePiece t e b = mUpdateAt t (\x => popPiece e x) b

-- addPiece : Nat -> PiecePos -> Board -> Maybe Board
-- addPiece t e b = mUpdate t (\x => pushPiece e x) b

-- TODO: Unfinished
