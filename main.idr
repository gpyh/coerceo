module Main

import HexGrid
import Data.Fin

TilePos : Type
TilePos = HexDirection 

data FieldPos : Type where
  MkFieldPos : HexPos -> TilePos -> FieldPos

data Color = White | Black

negate : Color -> Color
negate White = Black
negate Black = White

data Piece : Color -> Type where
  MkPiece : (color : Color) -> Piece color

data Player : Color -> Type where
  MkPlayer : (color : Color) -> Player color
  
data Tile : Type where
  NotOnBoard : (owner : Maybe (Player color)) -> Tile
  OnBoard : (c : Maybe (Piece White)) ->
            (d : Maybe (Piece Black)) ->
            (e : Maybe (Piece White)) ->
            (f : Maybe (Piece Black)) ->
            (a : Maybe (Piece White)) ->
            (b : Maybe (Piece Black)) -> Tile


doubleRotate : Tile -> Tile
doubleRotate (OnBoard c d e f a b) = OnBoard a b c d e f
doubleRotate t = t

friendlyPair : TilePos -> Tile
friendlyPair C = OnBoard (Just (MkPiece White))
                         Nothing
                         (Just (MkPiece White))
                         Nothing 
                         Nothing
                         Nothing
friendlyPair D = OnBoard Nothing
                         (Just (MkPiece Black))
                         Nothing
                         (Just (MkPiece Black))
                         Nothing 
                         Nothing
friendlyPair e = doubleRotate (friendlyPair ((succ^4) e))

unFriendlyPair : TilePos -> Tile
unFriendlyPair C = OnBoard (Just (MkPiece White))
                           Nothing
                           Nothing
                           (Just (MkPiece Black))
                           Nothing
                           Nothing
unFriendlyPair D = OnBoard Nothing
                           (Just (MkPiece Black))
                           Nothing
                           Nothing
                           (Just (MkPiece White))
                           Nothing 
unFriendlyPair e = doubleRotate (unFriendlyPair ((succ^4) e))

Board : Type 
Board = HexGrid 2 Tile

emptyTile : Tile
emptyTile = OnBoard Nothing Nothing Nothing Nothing Nothing Nothing

laurentius : Board
laurentius = lfr _ where
  lfr : (n : Nat) -> HexChain (S n) Z Tile
  lfr n with (hexPosFromNat n)
    lfr Z | Origin = emptyTile::Nil
    lfr (S k) | (Pos Z e FZ) = friendlyPair (pred e) :: lfr k
    lfr (S k) | (Pos (S Z) e FZ) = friendlyPair (pred e) :: lfr k
    lfr (S k) | (Pos (S Z) e (FS FZ)) = unFriendlyPair e :: lfr k
    lfr (S k) | (Pos (S (S ppr)) _ _) = emptyTile :: lfr k

emptyBoard : Board
emptyBoard = replicate _ emptyTile 

