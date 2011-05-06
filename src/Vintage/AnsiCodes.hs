{- |Library for formatted output on terminals

    Information on ANSI Codes can be found at
    http://www.dee.ufcg.edu.br/~rrbrandt/tools/ansi.html

    @author Sebastian Fischer
-}
module Vintage.AnsiCodes
  ( -- * functions for cursor movement
    cursorPos, cursorHome, cursorUp, cursorDown, cursorFwd, cursorBack
  , saveCursor, restoreCursor

    -- * functions for graphics control
  , clear, eraseLine

  -- * functions for formatted output
  , bold, underline, revColors, concealed, black, red, green, yellow, blue
  , cyan, magenta, white, bgBlack, bgRed, bgGreen, bgYellow, bgBlue, bgCyan
  , bgMagenta, bgWhite

  -- * string operations
  , ansiLength
  ) where

import Data.Char (chr, isDigit)
import Data.List (isSuffixOf)

-- |escape character
esc :: Char
esc = chr 27

-- |The functions for cursor movement
cmd :: String -> String
cmd s = esc : '[' : s

-- |move cursor to position
cursorPos :: (Show a, Show b) => a -> b -> String
cursorPos r c = cmd (show r ++ ";" ++ show c ++ "H")

-- |move cursor to home position
cursorHome :: String
cursorHome = cmd "H"

moveCursor :: String -> String -> String
moveCursor s n = cmd (show n ++ s)

-- |move cursor n lines up
cursorUp :: String -> String
cursorUp = moveCursor "A"

-- |move cursor n lines down
cursorDown :: String -> String
cursorDown = moveCursor "B"

-- |move cursor n columns forward
cursorFwd :: String -> String
cursorFwd = moveCursor "C"

-- |move cursor n columns backward
cursorBack :: String -> String
cursorBack = moveCursor "D"

-- |save cursor position
saveCursor :: String
saveCursor = cmd "s"

-- |restore saved cursor position
restoreCursor :: String
restoreCursor = cmd "u"

-- |The functions for controlling graphics

-- |clear screen
clear :: String
clear = cmd "2J"

-- |erase line
eraseLine :: String
eraseLine = cmd "K"

mode :: Int -> String -> String
mode n s = cmd (show n ++ "m" ++ s ++ if end `isSuffixOf` s then "" else end)
 where end = cmd "0m"

-- |format text
bold :: String -> String
bold = mode 1

underline :: String -> String
underline = mode 4

revColors :: String -> String
revColors = mode 7

concealed :: String -> String
concealed = mode 8

black :: String -> String
black = mode 30

red :: String -> String
red = mode 31

green :: String -> String
green = mode 32

yellow :: String -> String
yellow = mode 33

blue :: String -> String
blue = mode 34

magenta :: String -> String
magenta = mode 35

cyan :: String -> String
cyan = mode 36

white :: String -> String
white = mode 37

bgBlack :: String -> String
bgBlack = mode 40

bgRed :: String -> String
bgRed = mode 41

bgGreen :: String -> String
bgGreen = mode 42

bgYellow :: String -> String
bgYellow = mode 43

bgBlue :: String -> String
bgBlue = mode 44

bgMagenta :: String -> String
bgMagenta = mode 45

bgCyan :: String -> String
bgCyan = mode 46

bgWhite :: String -> String
bgWhite = mode 47

ansiLength :: String -> Int
ansiLength s = aux s $ length s where
  aux [] n = n
  aux (c : cs) n
    | c == esc && isDigit (cs !! 2) = aux (drop 4 cs) (n - 5)
    | c == esc                      = aux (drop 3 cs) (n - 4)
    | otherwise                     = aux cs n
