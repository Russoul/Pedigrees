module Main
import System
import Data.List
import Data.Either
import Data.Maybe
import Data.Vect
import Data.Nat
import Data.Strings
import Data.String.Extra
import System.File
import Syntax.WithProof
import Control.Monad.State
import Data.SortedSet
import System.Random
import System.Clock
import Data.List1
import Data.DPair
import Control.Monad.Syntax

Set : Type -> Type
Set a = SortedSet a


%foreign "C:srand, libc 6"
c_srand : Int -> PrimIO ()

srand' : HasIO io => Int -> io ()
srand' i = primIO (c_srand i)

%foreign "C:rand, libc 6"
c_rand : PrimIO Int

rand' : HasIO io => io Int 
rand' = primIO c_rand

dup : a -> (a, a)
dup x = (x, x)

--[min, max)
randRange' : HasIO io => Int -> Int -> io Int
randRange' min max = pure $ min + (!rand' `mod` (max - min))

select2' : HasIO io => Vect 2 a -> io a
select2' x = do
 let [a, b] = x 
 r <- rand'
 let i = r `mod` 2
 if i == 0 then pure a
    else pure b 

changeSeed : IO ()
changeSeed = 
 do
   time <- clockTime UTC
   let ns = time.nanoseconds
   let micro = ns `div` 1000 + 1
   srand micro

timeMillis : IO Int
timeMillis = 
 do
   time <- clockTime UTC
   pure . cast $ time.seconds * 1000 + (time.nanoseconds `div` 1000000)


exFalso : (0 _ : Void) -> a
exFalso x impossible

orElse : Maybe a -> Lazy a -> a
orElse (Just x) _ = x
orElse Nothing x = x

implementation [showStr] Show String where
 show x = x

debug__ : String -> ()
debug__ x = unsafePerformIO (putStrLn $ "[debug] " ++ x)


||| replaces all occurances of literal @lit 
||| in string @str 
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

ansiColorStr : String -> Vect 3 Int -> String
ansiColorStr str [r, g, b] = "\x1b[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++  "m" ++ str ++ "\x1b[0m"

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

sepBy : String -> List String -> String
sepBy sep (x :: xs@(_ :: _)) = x ++ sep ++ sepBy sep xs
sepBy _ [x] = x
sepBy _ [] = ""

-- ^^ Helpers -----
-------------------

data BinTree : Type -> Type where
   Empty : BinTree a
   Node : BinTree a -> a -> BinTree a -> BinTree a

Functor BinTree where
   map f (Node l x r) = Node (f <$> l) (f x) (f <$> r)
   map _ Empty = Empty

toLinear : BinTree a -> List (List a)
toLinear (Node l x r) = [x] :: (uncurry (++) <$> (toLinear l `zip` toLinear r))
toLinear Empty = []

reflect : BinTree a -> BinTree (a, BinTree a)
reflect node@(Node l x r) = Node (reflect l) (x, node) (reflect r)
reflect Empty = Empty

Foldable BinTree where
   foldr f ac (Node l x r)
    = let right = foldr f ac r
          ac = f x right in
          foldr f ac l
   foldr _ ac Empty = ac

   foldl f ac (Node l x r)
    = let left = foldl f ac l 
          ac = f left x in
          foldl f ac r
   foldl _ ac Empty = ac

maxDepth : BinTree a -> Nat
maxDepth (Node l _ r) = max (maxDepth l) (maxDepth r) + 1
maxDepth Empty = 0

prolongToDepth : Nat -> BinTree a -> a -> BinTree a
prolongToDepth (S k) (Node l x r) def = Node (prolongToDepth k l def) x (prolongToDepth k r def)
prolongToDepth (S k) Empty def = Node (prolongToDepth k Empty def) def (prolongToDepth k Empty def) 
prolongToDepth Z tree _ = tree

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


record TableRow where
   constructor MkRow
   gen : Maybe Int
   id : Int
   name : String
   parents : Maybe (Int {-sire-}, Int {-dam-})

Name : Type
Name = TableRow

Eq TableRow where
 x == y = TableRow.id x == y.id

Ord TableRow where
 compare x y = compare (TableRow.id x) y.id

Show TableRow where
 show (MkRow gen id name Nothing) = sepBy "," [show gen, show id, show name]
 show (MkRow gen id name (Just (id1, id2))) = sepBy "," [show gen, show id, show name, show id1, show id2]

Error : Type
Error = String

data TreeFormat = Relation Name Name
                | Kinship Name
                | SetColor Name Color





-- where
--    mkTree : List (String, String) -> List (String, BinTree String) -> Either Error (List (String,String), ((String, BinTree String), List (String, BinTree String)))
--    mkTree names@((offspring, _) :: _) generated
--     = let (ancestors, rest) = partition ((== offspring) . fst) names in
--           case lookupAndReorder offspring generated of
--                Just x => Right (rest, x)
--                _ =>

--                   case ancestors of
--                        [(_, ancestor)] 
--                         => let (ancestor's, rest) = partition ((== ancestor) . fst) rest in
--                                case lookupAndReorder ancestor generated of     
--                                     Just (self, generated) => Right (rest, ((offspring, Node self.snd offspring Empty), self :: generated))
--                                     _ => 
--                                       do
--                                         (rest, (tree, generated)) <- if ancestor's.isCons 
--                                                                         then mkTree (ancestor's ++ rest) generated
--                                                                         else Right (rest, ((ancestor, Node Empty ancestor Empty), generated))
--                                         let generated = tree :: generated                    
--                                         Right (rest, ((offspring, Node tree.snd offspring Empty), generated))         
                                                                     
--                        [(_, ancestor1), (_, ancestor2)] 
--                         => let (ancestor1's, rest) = partition ((== ancestor1) . fst) rest in
--                                do
--                                   (rest, (ltree, generated)) <- case lookupAndReorder ancestor1 generated of 
--                                                                      Just x => Right (rest, x)
--                                                                      _ => 
--                                                                          if ancestor1's.isCons 
--                                                                             then mkTree (ancestor1's ++ rest) generated
--                                                                             else Right (rest, ((ancestor1, Node Empty ancestor1 Empty), generated))
--                                   let generated = ltree :: generated
--                                   let (ancestor2's, rest) = partition ((== ancestor2) . fst) rest
--                                   (rest, (rtree, generated)) <- case lookupAndReorder ancestor2 generated of
--                                                                      Just x => Right (rest, x)
--                                                                      _ => 
--                                                                          if ancestor2's.isCons
--                                                                             then mkTree (ancestor2's ++ rest) generated
--                                                                             else Right (rest, ((ancestor2, Node Empty ancestor2 Empty), generated))
--                                   let generated = rtree :: generated                            
--                                   pure (rest, ((offspring, Node ltree.snd offspring rtree.snd), generated)) 
--                        [] => Left "impossible"           
--                        _ => Left $ "expected at most 2 explicit decendents, got: "
--                                    ++ show ancestors.length 
--                                    ++ " for name: "
--                                    ++ offspring
--    where
--       lookupAndReorder : String -> List (String, BinTree String) -> Maybe ((String, BinTree String), List (String, BinTree String))
--       lookupAndReorder name generated
--        = let (l, r) = break ((== name) . fst) generated in
--              case r of
--                   (x :: r) => Just (x, l ++ r)
--                   [] => Nothing

--    mkTree [] (x :: xs) = Right ([], (x, xs))
--    mkTree [] [] = Left $ "expected non-empty relation map, got empty"


--    dropComments : String -> String
--    dropComments str = fst $ span (/= '#') str


--    addOrReplace : (Eq a) => a -> List a -> List a
--    addOrReplace x (y :: zs)
--     = case x == y of
--            True => x :: zs
--            False => y :: addOrReplace x zs
--    addOrReplace x [] = [x]        

--    parseTreeFormatImpl : String -> Either Error TreeFormat
--    parseTreeFormatImpl str
--     = let (l, r) = span (/= '>') str in
--           case r /= "" of
--                True => let l = trim $ dropLast 1 l
--                            r = trim $ drop 1 r
--                        in
--                            Right (Relation l r)
--                False => 
--                   let (l, r) = span (/= '-') str
--                       l = trim l
--                       r = trim $ drop 1 r in
--                       case r /= "" of
--                            True =>  let (Just color) = parseColor r
--                                         | _ => Left $ "expected color, got: " ++ l ++ " on line: " ++ str in
--                                     Right $ SetColor l color   
--                            False =>
--                               case isSuffixOf "$" str of
--                                    True => pure $ Kinship (dropLast 1 str)
--                                    False => 
--                                       Left
--                                        $ "cannot parse line: " ++ str


parseRowTableFormat : String -> Either Error TableRow
parseRowTableFormat str
 = case split (== ',') str of
        [gen, id, name, sireId, damId]
          => let mbgen = maybeToEither 
                          (refineError "<gen> must be a natural number") 
                           ((Just <$> parsePositive {a = Int} gen) <|> toMaybe (trim gen == "") Nothing)
                 mbid = maybeToEither (refineError "<id> must be a natural number") (parsePositive {a = Int} id)
                 mbname = maybeToEither (refineError "<name> must be non-empty") (toMaybe (trim name /= "") (trim name))
                 mbsireId 
                   = maybeToEither 
                      (refineError "<sire id> must be a natural number or left blank") 
                       ((Just <$> parsePositive {a = Int} sireId) <|> toMaybe (trim sireId == "") Nothing)
                      
                 mbdamId 
                   = maybeToEither
                      (refineError "<dam id> must be a natural number or left blank") 
                       ((Just <$> parsePositive {a = Int} damId) <|> toMaybe (trim damId == "") Nothing)
                 mbpars
                  = do
                    sire <- mbsireId
                    dam <- mbdamId
                    let True = sire.isJust == dam.isJust
                        | _ => Left "<sire id> and <dam id> must be both available or empty"
                    pure $ do s <- sire; d <- dam; Just (s, d)
             in
                 [|MkRow mbgen mbid mbname mbpars|]

        _ => Left ("expected format: <gen>, <id>, <name>, <sire id>, <dam id>; got: " ++ str)
where
   refineError : Error -> Error
   refineError err = err ++ ", got: " ++ str



lookupAndReorder : (Eq id) => id -> List (id, BinTree a) -> Maybe ((id, BinTree a), List (id, BinTree a))
lookupAndReorder name generated
 = let (l, r) = break ((== name) . fst) generated in
       case r of
            (x :: r) => Just (x, l ++ r)
            [] => Nothing

mkTree : (Eq id, Show id) => List (id, a, Maybe (id, id)) -> List (id, BinTree a) -> Either Error (List (id, a, Maybe (id, id)), ((id, BinTree a), List (id, BinTree a)))
mkTree ((offspring, (dat, Nothing)) :: rest) generated = Right (rest, ((offspring, Node Empty dat Empty), generated))
mkTree ((offspring, (dat, Just (ancestor1, ancestor2))) :: rest) generated
 = case lookupAndReorder offspring generated of
            Just x => Right (rest, x)
            _ => do
                 let ([ancestor1's], rest) = partition ((== ancestor1) . fst) rest
                     | (list, rest) => Left $ "expected all row entries to be unique in id, got duplicates: " ++ show (fst <$> list)
                 (rest, (ltree, generated)) <- case lookupAndReorder ancestor1 generated of 
                                                    Just x => Right (rest, x)
                                                    _ => mkTree (ancestor1's :: rest) generated
                 let generated = ltree :: generated
                 let ([ancestor2's], rest) = partition ((== ancestor2) . fst) rest
                     | (list, rest) => Left $ "expected all row entries to be unique in id, got duplicates: " ++ show (fst <$> list)
                 (rest, (rtree, generated)) <- case lookupAndReorder ancestor2 generated of
                                                    Just x => Right (rest, x)
                                                    _ => mkTree (ancestor2's :: rest) generated
                 let generated = rtree :: generated                            
                 pure (rest, ((offspring, Node ltree.snd dat rtree.snd), generated)) 
mkTree [] (x :: xs) = Right ([], (x, xs))
mkTree [] [] = Left $ "expected non-empty relation map, got empty"

parseTreeCsv : String -> Either Error (List (Int, BinTree TableRow))
parseTreeCsv str
 = let l = lines str
       cultivated = trim . dropComments <$> drop 1 l -- skip first line
       noEmpties = filter (/= "") cultivated in
       do
          list <- sequence $ ((\x => pure (TableRow.id x, x, x.parents)) <=< parseRowTableFormat) <$> noEmpties
          (_, x, xs) <- mkTree list []
          pure $ x :: xs
       
where
    dropComments : String -> String
    dropComments str = fst $ span (/= '#') str


namespace Tagged
   export
   toAnsi : (Bool, Maybe Color) -> String -> String
   toAnsi (True, c) str = ansiUnderlineStr (toAnsi (False, c) str)
   toAnsi (False, c) str = case c of Just c => ansiColorStr str (toRgb c); _ => str

showBinTree : (Eq a) => {auto show : a -> String} -> List (List a) -> List String
showBinTree (x :: xs)
 = let space = replicate (pown 2 xs.length `minus` 1) ' '
       newl = replicate (pown 2 (xs.length `minus` 1) `minus` 1) '\n' in
       (space ++ sepBy (replicate (pown 2 (xs.length + 1) `minus` 1) ' ') (show <$> x) ++ newl) :: showBinTree xs
where
   pown : Nat -> Nat -> Nat
   pown n (S k) = n * (pown n k)
   pown _ Z = 1
showBinTree [] = []       

-------------------
---- Algorithm ---- 
-------------------

infix 0 =/= 

(=/=) : (0 _ : a) -> (0 _ : b) -> Type
(=/=) x y = (x ~=~ y) -> Void


data Pedigree : BinTree Name -> Type where
     Founder : Pedigree (Node Empty name Empty)
     Proband : (left : Pedigree (Node ll lx lr)) -> (right : Pedigree (Node rl rx rr)) -> Pedigree (Node (Node ll lx lr) name (Node rl rx rr))


Uninhabited (Pedigree Empty) where
 uninhabited Founder impossible
 uninhabited (Proband _ _) impossible


Uninhabited (Proband Founder Founder = Founder) where
 uninhabited contra impossible

probandNotFounder : {0 l, r : _} -> (0 p : Pedigree _) -> {auto 0 prf : p = Proband l r} -> p =/= Founder
probandNotFounder (Proband Founder Founder) Refl impossible

0 pedUnique : (0 p : Pedigree x) -> (0 p' : Pedigree x) -> p = p'
pedUnique Founder Founder = Refl
pedUnique Founder (Proband _ _) impossible
pedUnique (Proband _ _) Founder impossible
pedUnique (Proband ll lr) (Proband rl rr) 
 = let leq = pedUnique ll rl 
       req = pedUnique lr rr in
       rewrite leq in
       rewrite req in Refl 

name : (x : BinTree Name) -> {auto 0 p : Pedigree x} -> Name
name (Node _ n _) = n

data RelationTy : Type where
     Self : (x : BinTree Name) 
        -> {auto 0 p : Pedigree x} 
        -> RelationTy
     Nested : (x : BinTree Name) 
        -> {auto 0 px : Pedigree x} 
        -> (px =/= Founder {name = x.name}) 
        -> (y : BinTree Name) 
        -> {auto 0 py : Pedigree y} 
        -> RelationTy
     Linear : (x : BinTree Name) 
        -> {auto 0 px : Pedigree x} 
        -> (y : BinTree Name) 
        -> {auto 0 py : Pedigree y} 
        -> RelationTy

Show RelationTy where
 show (Self p) = "Self " ++ p.name.name
 show (Nested x _ y) = "OffPar " ++ x.name.name ++ " " ++ y.name.name
 show (Linear x y) = "Linear " ++ x.name.name ++ " " ++ y.name.name



mutual
   
   total
   kinship : 
        (Name -> Bool)
     -> (x : BinTree Name)
     -> (y : BinTree Name) 
     -> {auto 0 px : Pedigree x}
     -> {auto 0 py : Pedigree y}
     -> Double
   kinship isVirtualFounder node1 node2
    = let rel = relationTy node1 node2 in
          -- let _ = debug__ (show rel) in
          case rel of
               Self self => assert_total 
                $ kinshipSelf isVirtualFounder self
               Nested off _ par => assert_total 
                $ kinshipNested isVirtualFounder off par
               Linear l r => assert_total 
                $ kinshipLinear isVirtualFounder l r
               
   total
   relationTy : 
         (x : BinTree Name)
      -> (y : BinTree Name) 
      -> {auto 0 px : Pedigree x}
      -> {auto 0 py : Pedigree y}
      -> RelationTy
   relationTy x y
    = case x.name == y.name of
           True => Self x
           False =>
              case isNested x y of
                   (True ** prf) => Nested x prf y
                   (False ** _) =>
                      case isNested y x of
                           (True ** prf) => Nested y prf x
                           (False ** _) => Linear x y

   total
   isNested :
        (x : BinTree Name)
     -> {auto 0 px : Pedigree x}
     -> (y : BinTree Name)
     -> {auto 0 py : Pedigree y}
     -> (nested : Bool ** if nested then px =/= Founder {name = x.name} else ())
   isNested (Node (Node ll lx lr) _ (Node rl rx rr)) {px = Proband l r} ancestor
    = let is = lx == ancestor.name 
            || rx == ancestor.name
            || (isNested (Node ll lx lr) ancestor).fst
            || (isNested (Node rl rx rr) ancestor).fst in
          if is then (True ** probandNotFounder (Proband l r)) else (False ** ())
   isNested (Node Empty _ Empty) {px} _ = (False ** ())  
   isNested (Node Empty _ (Node _ _ _)) {px} _ = exFalso $ lemma px
   where
      0
      lemma : (0 p : Pedigree (Node Empty _ (Node _ _ _))) -> Void
      lemma (Proband _ _) impossible
      lemma Founder impossible
      
   isNested (Node (Node _ _ _) _ Empty) {px} _ = exFalso $ lemma px
   where
      0
      lemma : (0 p : Pedigree (Node (Node _ _ _) _ Empty)) -> Void
      lemma (Proband _ _) impossible
      lemma Founder impossible

   
   total
   kinshipSelf : 
        (Name -> Bool) 
     -> (x : BinTree Name) 
     -> {auto 0 p : Pedigree x} 
     -> Double
   kinshipSelf isVirtualFounder (Node (Node ll lx lr) name (Node rl rx rr)) {p = Proband _ _} with (isVirtualFounder name)
    kinshipSelf isVirtualFounder (Node (Node ll lx lr) _ (Node rl rx rr)) {p = Proband _ _ } | False 
     = 0.5 * (1 + kinship isVirtualFounder (Node ll lx lr) (Node rl rx rr))
    kinshipSelf isVirtualFounder (Node (Node ll lx lr) _ (Node rl rx rr)) {p = Proband _ _ } | True = 0.5
   kinshipSelf isVirtualFounder (Node Empty name Empty) {p = Founder} with (isVirtualFounder name)
    kinshipSelf isVirtualFounder (Node Empty name Empty) {p = Founder} | True = 0.5
    kinshipSelf isVirtualFounder (Node Empty name Empty) {p = Founder} | False = 0
   
   total
   kinshipNested : 
        (Name -> Bool) 
     -> (x : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto prf : px =/= Founder {name = x.name} } 
     -> (y : BinTree Name)
     -> {auto 0 py : Pedigree y} 
     -> Double
   kinshipNested isFounder (Node (Node ll lx lr) _ (Node rl rx rr)) {px = Proband _ _} parent
    = 0.5 * (kinship isFounder (Node ll lx lr) parent + kinship isFounder (Node rl rx rr) parent)
   kinshipNested _ (Node Empty _ Empty) {px = Founder} _ = exFalso $ prf Refl 
  

   total
   kinshipLinear : 
        (Name -> Bool) 
     -> (x : BinTree Name) 
     -> (y : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto 0 py : Pedigree y} 
     -> Double
   kinshipLinear f (Node (Node a an a') name (Node b bn b')) (Node (Node c cn c') name' (Node d dn d')) {px = Proband _ _} {py = Proband _ _}
     = 0.25 * (  kinship f (Node a an a') (Node c cn c') 
               + kinship f (Node a an a') (Node d dn d') 
               + kinship f (Node b bn b') (Node c cn c') 
               + kinship f (Node b bn b') (Node d dn d'))
   kinshipLinear f _ _ = 0
   
   bloodQuotaSelf : 
        (x : BinTree Name) 
     -> {auto 0 px : Pedigree x}
     -> Name
     -> Double
   bloodQuotaSelf (Node (Node ll lx lr) name (Node rl rx rr)) {px = Proband _ _} n with (name == n)
    bloodQuotaSelf (Node (Node ll lx lr) name (Node rl rx rr)) {px = Proband _ _} n | True = 0.75
    bloodQuotaSelf (Node (Node ll lx lr) name (Node rl rx rr)) {px = Proband _ _} n | False
     = (bloodQuota (Node ll lx lr) (Node rl rx rr) n 
        + 1.0 / (2 * 3) * kinship (== n) (Node ll lx lr) (Node rl rx rr)) * 3 / 4
   bloodQuotaSelf (Node Empty name Empty) {px = Founder} n with (name == n)
    bloodQuotaSelf (Node Empty name Empty) {px = Founder} n | True = 0.75
    bloodQuotaSelf (Node Empty name Empty) {px = Founder} n | False = 0

   bloodQuotaNested : 
        (x : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto prf : px =/= Founder {name = x.name} } 
     -> (y : BinTree Name)
     -> {auto 0 py : Pedigree y}
     -> Name
     -> Double
   bloodQuotaNested (Node (Node ll lx lr) _ (Node rl rx rr)) {px = Proband _ _} parent n
    = 0.5 * (bloodQuota (Node ll lx lr) parent n + bloodQuota (Node rl rx rr) parent n)
   bloodQuotaNested (Node Empty _ Empty) {px = Founder} _ _ = exFalso $ prf Refl 

   bloodQuotaLinear : 
        (x : BinTree Name) 
     -> (y : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto 0 py : Pedigree y} 
     -> Name
     -> Double
   bloodQuotaLinear (Node (Node a an a') name (Node b bn b')) (Node (Node c cn c') name' (Node d dn d')) {px = Proband _ _} {py = Proband _ _} n
     = 0.25 * (  bloodQuota (Node a an a') (Node c cn c') n
               + bloodQuota (Node a an a') (Node d dn d') n
               + bloodQuota (Node b bn b') (Node c cn c') n
               + bloodQuota (Node b bn b') (Node d dn d') n)
   bloodQuotaLinear (Node (Node ll lx lr) _ (Node rl rx rr)) a {px = Proband _ _} n
    = 0.5 * (bloodQuota (Node ll lx lr) a n + bloodQuota (Node rl rx rr) a n)
   bloodQuotaLinear a (Node (Node ll lx lr) _ (Node rl rx rr)) {py = Proband _ _} n
    = 0.5 * (bloodQuota (Node ll lx lr) a n + bloodQuota (Node rl rx rr) a n)
   bloodQuotaLinear (Node _ x _) (Node _ y _) n with (x == n || y == n)
    bloodQuotaLinear (Node _ x _) (Node _ y _) n | True = 0.5
    bloodQuotaLinear (Node _ x _) (Node _ y _) n | False = 0

   bloodQuota : 
         (x : BinTree Name)
      -> (y : BinTree Name)
      -> {auto 0 px : Pedigree x}
      -> {auto 0 py : Pedigree y}
      -> Name
      -> Double
   bloodQuota x y n 
    = case relationTy x y of
           Self self => assert_total 
            $ bloodQuotaSelf self n
           Nested off _ par => assert_total 
            $ bloodQuotaNested off par n
           Linear l r => assert_total 
            $ bloodQuotaLinear l r n



--    total
--    bloodQuota : -- Y is nested in X or X = Y OLD ALGORITHM
--          (x : BinTree Name)
--       -> (y : BinTree Name)
--       -> {auto p1 : Pedigree x}
--       -> {auto p2 : Pedigree y}
--       -> (Double {-Bq-}, Double {-X-})
--    bloodQuota (Node a x b) y {p1 = Proband _ _}
--     = case x == y.name of
--            False =>
--               let (_, ay) = bloodQuota a y
--                   (_, by) = bloodQuota b y
--               in    
--                   (ay + by - ay * by, 0.5 * (ay + by))
--            True => (1, 0.5)
--    bloodQuota (Node _ x _) (Node _ y _) {p1 = Founder}
--     = case x == y of
--            False => (0, 0)
--            True => (1, 0.5)
   
--    total
--    bloodQuota' : -- (Y is nested in X) or (X is nested in Y) or (X = Y)
--              (x : BinTree Name)
--           -> (y : BinTree Name)
--           -> {auto p1 : Pedigree x}
--           -> {auto p2 : Pedigree y}
--           -> Maybe ((Double, Double))
--    bloodQuota' x y
--     = case isNested x y of
--            (True ** _) => Just $ bloodQuota x y
--            (False ** _) => 
--               case isNested y x of
--                    (True ** _) => Just $ bloodQuota y x
--                    (False ** _) => if x.name == y.name 
--                                       then Just $ bloodQuota x y 
--                                       else Nothing 

-----------------
--- Algo end ----
-----------------

----------------------------------
------ SIMULATION for BQ ---------
----------------------------------
   data Allele = ALeft | ARight | AOther

   Show Allele where
      show ALeft = "1"
      show ARight = "2"
      show AOther = "*"

   total
   count : Vect 2 Allele -> Nat
   count [ALeft, ARight] = 2
   count [ARight, ALeft] = 2
   count [ALeft, AOther] = 1
   count [ALeft, ALeft] = 1
   count [ARight, AOther] = 1
   count [ARight, ARight] = 1
   count [AOther, ARight] = 1
   count [AOther, ALeft] = 1
   count [AOther, AOther] = 0

   total        
   simulateAllelePropagation : --simulate allele propagation towards X, accounting only for Y's alleles
         (x : BinTree Name)
      -> (y : BinTree Name)
      -> {auto 0 px : Pedigree x}
      -> {auto 0 py : Pedigree y}
      -> List (Name, Vect 2 Allele)
      -> IO (Vect 2 Allele, List (Name, Vect 2 Allele))
   simulateAllelePropagation (Node (Node ll lx lr) x (Node rl rx rr)) y {px = Proband _ _} pr
    = case lookup x pr of
           Nothing => case x == y.name of
                           True => pure ([ALeft, ARight], pr)
                           False => do
                                (l, pr) <- assert_total $ simulateAllelePropagation (Node ll lx lr) y pr
                                left <- select2' l
                                (r, pr) <- assert_total $ simulateAllelePropagation (Node rl rx rr) y pr
                                right <- select2' r
                                pure ([ left
                                     , right], (x, [left, right]) :: pr)    
           Just xx => pure (xx, pr)
   simulateAllelePropagation (Node _ x _) y {px = Founder} pr
    = case x == y.name of
           True => pure ([ALeft, ARight], pr)
           False => pure ([AOther, AOther], pr)
   
   total
   simulateBq : 
         (x : BinTree Name) 
      -> {auto 0 px : Pedigree x} 
      -> (y : BinTree Name) 
      -> {auto 0 py : Pedigree y}
      -> IO Double
   simulateBq x y = 
    do
      (s, _) <- simulateAllelePropagation x y []
      pure $ 0.5 * (count s).cast{to=Double}
----------------------------------
------ SIMULATION END ------------
----------------------------------


asPedigree : (x : BinTree Name) -> Maybe (Pedigree x)
asPedigree (Node (Node ll lx lr) name (Node rl rx rr))
 = 
  do  n1' <- asPedigree (Node ll lx lr)
      n2' <- asPedigree (Node rl rx rr)
      pure (Proband n1' n2')
asPedigree (Node Empty name Empty) = pure Founder
asPedigree _ = Nothing

founders : (x : BinTree Name) -> {auto 0 px : Pedigree x} -> Set Name
founders (Node (Node ll lx lr) name (Node rl rx rr)) {px = Proband _ _} = founders (Node ll lx lr) <+> founders (Node rl rx rr)
founders (Node Empty name Empty) {px = Founder} = fromList [name]

contains : Set a -> a -> Bool
contains = flip SortedSet.contains
%hide SortedSet.contains
%hide Data.List.toList

mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

calcBq : (x : BinTree Name) -> (0 _ : Pedigree x) -> Name  -> Maybe Double
calcBq (Node q@(Node _ _ _) _ w@(Node _ _ _)) (Proband _ _) t2 = Just $ bloodQuota q w t2
calcBq _ _ t2 = Nothing

byId : List Int -> Name -> Bool
byId list n = isJust $ List.find (== TableRow.id n) list 

main : IO ()
main = 
   do
      args <- getArgs
      putStrLn (show args)
      let [_, filename] = args
             | _ => do putStrLn "no filename argument"
                       exitFailure
      str <- readFile filename >>= orFail
      let tagged@[nt1, nt2] = the (Vect _ Int) [1, 2]
      trees <- pure (parseTreeCsv str) >>= orFail
      let Just (mainId, main) = trees.head'
            | _ => do putStrLn "Empty tree"
                      exitFailure
      putStrLn $ "Depth: " ++ show main.maxDepth
      putStrLn $ "Node count: " ++ show trees.length
      -- let colored = (\(id, name) => 
      --                  let mbcolor = lookup id colormap
      --                      tagged = (find (== id) tagged).isJust in
      --                      toAnsi (tagged, mbcolor) name
      --               ) <$> (mainId, main.name)
      -- let lin = toLinear (prolongToDepth main.maxDepth colored "-")
      -- traverse_ putStrLn (fst <$> trees)
      -- putStrLn "----------"
      -- traverse_ putStrLn (showBinTree {show = id} lin)
      let (Just t1, Just t2) = (lookup nt1 trees, lookup nt2 trees)
            | _ => do putStrLn "Tagged trees not found"; exitFailure
      let (Just p1, Just p2) = (asPedigree t1, asPedigree t2)
            | _ => do putStrLn "Tagged trees are not pedigrees"; exitFailure
      let (Just pmain) = asPedigree main
            | _ => do putStrLn "main is not pedigree"; exitFailure
      let fo = main.founders
      -- let lin = toLinear (prolongToDepth (max t1.maxDepth  t2.maxDepth) (Node t1 "-" t2) "-")
      let lin = toLinear (TableRow.id <$> main)
      --putStrLn "----------"
      -- traverse_ printLn (showBinTree {show} lin)
      let fo_list = fo.toList
      let fo_ids = TableRow.id <$> fo_list
      let t1_ids = TableRow.id <$> (founders t1).toList
      let t2_ids = TableRow.id <$> (founders t2).toList
      putStrLn $ "number of founders: " ++ show (fo_list.length)
      -- printLn $ "t1 founders: " ++ show t1_ids
      -- printLn $ "t2 founders: " ++ show t2_ids
      putStrLn $ "t1 number of founders: " ++ show (toList $ t1_ids.fromList `intersection` t2_ids.fromList)
      putStrLn $ "kinship: " ++ (show $ kinship (byId fo_ids) t1 t2)
      -- let (Just bq) = fst <$> bloodQuota' t1 t2
      --     | _ => do putStrLn $ "BQ is undefined "; exitFailure
      
      let (Just bq) = calcBq t1 p1 t2.name
          | _ => do putStrLn $ "BQ is undefined "; exitFailure
      -- putStrLn $ "bloodQuota: " ++ show (fst $ bloodQuota t1 t2)
      putStrLn $ "bloodQuota: " ++ show bq
      putStrLn $ "Partial kinship " ++ show (kinship (byId [5302]) t1 t2)
      putStrLn $ "unix time ms: " ++ show !timeMillis
      putStrLn $ show (t1.name, t2.name)
      srand' !timeMillis
      bqss <- sequence $ List.replicate 10000 $ simulateBq t1 t2 
      let mean = foldl (+) 0 bqss / bqss.length.cast{to=Double}
      let minv = foldl min 1 bqss
      let maxv = foldl max 0 bqss
      putStrLn $ "min: " ++ show minv ++ ", max: " ++ show maxv
      let variance = foldl (\l, r => l + (r - mean) * (r - mean)) 0 bqss / (bqss.length.cast{to=Double} - 1)

      putStrLn $ "bloodQuota simulated mean: " ++ show mean
      putStrLn $ "variance: " ++ show variance
      putStrLn $ "abs err: " ++ show (abs (bq - mean))
      putStrLn $ "rel err: " ++ show (abs (bq - mean) / abs bq)


