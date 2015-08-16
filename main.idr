module Main

import HexGrid

TilePos : Type
TilePos = HexDirection 

data Color = White | Black

data Piece : Color -> Type where
  WhitePiece : Piece White
  BlackPiece : Piece Black

data Player : Color -> Type where
  WhitePlayer : Player White
  BlackPlayer : Player Black
  
data Tile : Type where
  NotOnBoard : Tile
  OnBoard : (c : Maybe (Piece White)) ->
            (d : Maybe (Piece Black)) ->
            (e : Maybe (Piece White)) ->
            (f : Maybe (Piece Black)) ->
            (a : Maybe (Piece White)) ->
            (b : Maybe (Piece Black)) -> Tile

Board : Type
Board = HexGrid 2 Tile

emptyBoard : Board
emptyBoard = rep 19 Origin emptyTile where
  emptyTile = NotOnBoard
