module Util

import Data.Maybe
import Data.List
import Data.Vect
import Data.String.Extra
import Data.Strings

import System.Clock
import System.Random
import System

infix 0 =/= 

public export
(=/=) : (0 _ : a) -> (0 _ : b) -> Type
(=/=) x y = (x ~=~ y) -> Void
   
public export
data HList0 : (tyes : Vect n Type) -> Type where
     Nil : HList0 Nil
     (::) : (0 x : a) -> (0 xs : HList0 tyes) -> HList0 (a :: tyes)

public export
0
at : {tyes : Vect n Type} -> (i : Fin n) -> HList0 tyes -> index i tyes
at (FS i) (_ :: xs) = at i xs
at FZ (x :: _) = x

public export
%hint
0
at0Hint : HList0 ((x = y) :: xs) -> x = y 
at0Hint = at 0

public export
%hint
0
at1Hint : HList0 (_ :: (x = y) :: xs) -> x = y
at1Hint = at 1

public export
%hint
0
at1Hint' : HList0 (_ :: (x = y -> Void) :: xs) -> (x = y -> Void)
at1Hint' = at 1

public export
%hint
0
at2Hint : HList0 (_ :: _ :: (x = y) :: xs) -> x = y
at2Hint = at 2

public export
%hint
0
at2Hint' : HList0 (_ :: _ :: (x = y -> Void) :: xs) -> (x = y -> Void)
at2Hint' = at 2

public export
%hint
0
at3Hint : HList0 (_ :: _ :: _ :: (x = y) :: xs) -> x = y
at3Hint = at 3

public export
%hint
0
at3Hint' : HList0 (_ :: _ :: _ :: (x = y -> Void) :: xs) -> (x = y -> Void)
at3Hint' = at 3

public export
%hint
symNot : {x : a} -> {y : a} -> x =/= y -> y =/= x
symNot contra proof = contra (sym proof)

public export
data Align = AlignLeft | AlignRight

export
fixedWidth : String -> Nat -> Align -> String
fixedWidth str width align
 = let width' = max width (length str) in
       tabulate str (width' `minus` length str) align
where
   tabulate : String -> Nat -> Align -> String
   tabulate str n AlignLeft = str ++ pack (replicate n ' ')
   tabulate str n AlignRight = pack (replicate n ' ') ++ str

export
gcd' : Int -> Int -> Int
gcd' x y
 = let (max, min) = (max x y, min x y)
       r = max `mod` min in
       if r > 0 then gcd' min r else min

export
lcm' : Int -> Int -> Int
lcm' x y = abs (x * y) `div` gcd' x y

infix 10 //              

public export
data Rational = (//) Int Int

export
elim : (f : a -> b -> c) -> (a, b) -> c
elim f (a, b) = f a b

export
mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

export
fmapSnd : Monad m => (b -> m c) -> (a, b) -> m (a, c)
fmapSnd f (x, y) = do
                       y' <- f y
                       pure (x, y')

namespace Rational
   export
   normalForm : Rational -> Rational
   normalForm (a // b)
    = if a == 0 then 0 // 1
         else       
             let g = gcd' a b
                 (/) = div in
                 (a / g) // (b / g)

   export
   (+) : Rational -> Rational -> Rational
   (a // b) + (c // d)
    = let denom = lcm' b d
          (/) = div
          a' = denom / b
          c' = denom / d
          nom = a' * a + c' * c in
          normalForm (nom // denom)
   export      
   (*) : Rational -> Rational -> Rational 
   (a // b) * (c // d)
    = normalForm ((a * c) // (b * d))

Num Rational where
   (+) = Rational.(+)
   (*) = Rational.(*)
   fromInteger x = x.cast // 1

public export
interface Num a => Rat a where
   fromRational : Rational -> a

export
Rat Rational where
   fromRational x = x

export
Rat Double where
   fromRational (a // b) = a.cast{to=Double} / b.cast{to=Double}

export
Show Rational where
   show (a // b) = show a ++ "/" ++ show b

%foreign "C:srand, libc 6"
c_srand : Int -> PrimIO ()

export
srand' : HasIO io => Int -> io ()
srand' i = primIO (c_srand i)

%foreign "C:rand, libc 6"
c_rand : PrimIO Int

export
rand' : HasIO io => io Int 
rand' = primIO c_rand

--[min, max)
export
randRange' : HasIO io => Int -> Int -> io Int
randRange' min max = pure $ min + (!rand' `mod` (max - min))

export
select2' : HasIO io => Vect 2 a -> io a
select2' x = do
 let [a, b] = x 
 r <- rand'
 let i = r `mod` 2
 if i == 0 then pure a
    else pure b 

export
changeSeed : IO ()
changeSeed = 
 do
   time <- clockTime UTC
   let ns = time.nanoseconds
   let micro = ns `div` 1000 + 1
   srand (cast micro)

export
timeMillis : IO Int
timeMillis = 
 do
   time <- clockTime UTC
   pure . cast $ time.seconds * 1000 + (time.nanoseconds `div` 1000000)

export
exFalso : (0 _ : Void) -> a
exFalso x impossible

orElse : Maybe a -> Lazy a -> a
orElse = flip fromMaybe

implementation [showStr] Show String where
 show x = x

||| replaces all occurances of literal @lit 
||| in string @str 
export
removeAll :
      (lit : String) 
   -> (str : String)
   -> String
removeAll lit str with (str == "") 
   removeAll lit str | False =  
      let other = removeAll lit (substr (length lit) (length str `minus` length lit) str) in
          if isPrefixOf lit str
             then removeAll lit (substr (length lit) (length str `minus` length lit) str)
             else case strUncons str of
                       Just (head, rest) => strCons head (removeAll lit rest)
                       Nothing => ""
   removeAll lit str | True = "" 

export
ansiColorStr : String -> Vect 3 Int -> String
ansiColorStr str [r, g, b] = "\x1b[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++  "m" ++ str ++ "\x1b[0m"

export
ansiUnderlineStr : String -> String
ansiUnderlineStr str = "\x1b[4m" ++ str ++ "\x1b[0m"

namespace Either 
   export
   orFail : {a : Type} -> (Show a) => Either a b -> IO b
   orFail @{s} (Left err) = do putStrLn (show @{betterStr} err); exitFailure
   where 
      betterStr : Show a
      betterStr = case a of
                       String => showStr
                       _ => s
   orFail (Right x) = pure x

namespace Maybe 
   export
   orFail : {a : Type} -> Maybe a -> String -> IO a
   orFail Nothing err = do putStrLn err; exitFailure
   orFail (Just x) _ = pure x

export
sepBy : String -> List String -> String
sepBy sep (x :: xs@(_ :: _)) = x ++ sep ++ sepBy sep xs
sepBy _ [x] = x
sepBy _ [] = ""

public export
data Color = Red | Green | Blue | Yellow | Pink | Cyan

Eq Color where
   Red == Red = True
   Green == Green = True
   Blue == Blue = True
   Yellow == Yellow = True
   Pink == Pink = True
   Cyan == Cyan = True
   _ == _ = False

Show Color where
   show Red = "R"
   show Green = "G"
   show Blue = "B"
   show Yellow = "Y"
   show Pink = "P"
   show Cyan = "C"

export
toRgb : Color -> Vect 3 Int
toRgb Red = [128, 0, 0]
toRgb Green = [0, 128, 0]
toRgb Blue = [0, 0, 128]
toRgb Yellow = [255, 255, 0]
toRgb Pink = [255, 192, 203]
toRgb Cyan = [0, 255, 255]


parseColor : String -> Maybe Color
parseColor "R" = Just Red
parseColor "G" = Just Green
parseColor "B" = Just Blue
parseColor "Y" = Just Yellow
parseColor "P" = Just Pink
parseColor "C" = Just Cyan
parseColor _ = Nothing

export
intToNat : Int -> Nat
intToNat = integerToNat . cast {to = Integer}

namespace Tagged
   export
   toAnsi : (Bool, Maybe Color) -> String -> String
   toAnsi (True, c) str = ansiUnderlineStr (toAnsi (False, c) str)
   toAnsi (False, c) str = case c of Just c => ansiColorStr str (toRgb c); _ => str
