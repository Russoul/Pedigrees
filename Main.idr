module Main

import Control.Linear.LIO
import Control.Monad.Syntax

import Data.DPair
import Data.Either
import Data.Linear.Array
import Data.List
import Data.List1
import Data.Maybe
import Data.Nat
import Data.SortedMap
import Data.SortedSet
import Data.String.Extra
import Data.Strings
import Data.Vect

import Debug.Trace

import Decidable.Equality

import Syntax.WithProof

import System
import System.Clock
import System.File
import System.Random

import Util

Set : Type -> Type
Set a = SortedSet a

%hide Prelude.id


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
maxDepth (Node l@(Node _ _ _) _ r@(Node _ _ _)) = max (maxDepth l) (maxDepth r) + 1
maxDepth (Node l@(Node _ _ _) _ Empty) = maxDepth l + 1
maxDepth (Node Empty _ r@(Node _ _ _)) = maxDepth r + 1
maxDepth (Node Empty _ Empty) = 1
maxDepth Empty = 0

showMaxPath : (a -> String) -> BinTree a -> (Nat, String)
showMaxPath show (Node l@(Node _ _ _) x r@(Node _ _ _))
 =                              let (maxl, showl) = showMaxPath show l
                                    (maxr, showr) = showMaxPath show r
                                    (max, showmax) = if maxl > maxr 
                                                        then (maxl, showl)
                                                        else (maxr, showr) in
                                    (max + 1, show x ++ "\n" ++ showmax)
showMaxPath show (Node n@(Node _ _ _) x Empty) = (\i, xs => (i + 1, show x ++ "\n" ++ xs)) `elim` showMaxPath show n
showMaxPath show (Node Empty x n@(Node _ _ _)) = (\i, xs => (i + 1, show x ++ "\n" ++ xs)) `elim` showMaxPath show n
showMaxPath show (Node Empty x Empty) = (1, show x)
showMaxPath show Empty = (0, "")
                                                                        



prolongToDepth : Nat -> BinTree a -> a -> BinTree a
prolongToDepth (S k) (Node l x r) def = Node (prolongToDepth k l def) x (prolongToDepth k r def)
prolongToDepth (S k) Empty def = Node (prolongToDepth k Empty def) def (prolongToDepth k Empty def) 
prolongToDepth Z tree _ = tree


record TableRow where
   constructor MkRow
   gen : Maybe Int
   id : Int
   name : String
   parents : Maybe (Int {-sire-}, Int {-dam-})

Name : Type
Name = TableRow

Eq TableRow where
 x == y = TableRow.id x == TableRow.id y

Ord TableRow where
 compare x y = compare (TableRow.id x) y.id

-- data IsSet : List a -> Type where
--      Empty : IsSet []
--      Cons : IsSet xs -> Not (Elem x xs) -> IsSet (x :: xs)

data Injection : Type -> Type -> Type where
     IsInjection : (f : a -> b) -> (prf : (x : a) -> (y : a) -> f x = f y -> x = y) -> Injection a b

Show TableRow where
 show (MkRow gen id name Nothing) = sepBy "," [show id, show name]
 show (MkRow gen id name (Just (id1, id2))) = sepBy "," [show id, show name, show id1, show id2]

Error : Type
Error = String

data TreeFormat = Relation Name Name
                | Kinship Name
                | SetColor Name Color


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
                 (rest, (ltree, generated)) <- case lookupAndReorder ancestor1 generated of 
                                                    Just x => Right (rest, x)
                                                    _ => do 
                                                           let ([ancestor1's], rest) = partition ((== ancestor1) . fst) rest
                                                                | (list, rest) => 
                                                                     Left $ "expected all row entries to be unique in id and non-empty, got: " 
                                                                            ++ show (fst <$> list) ++ " for parent id " 
                                                                            ++ show ancestor1 ++ " for " ++ show offspring

                                                           mkTree (ancestor1's :: rest) generated
                 let generated = ltree :: generated
                 (rest, (rtree, generated)) <- case lookupAndReorder ancestor2 generated of
                                                    Just x => Right (rest, x)
                                                    _ => do 
                                                           let ([ancestor2's], rest) = partition ((== ancestor2) . fst) rest
                                                                | (list, rest) => 
                                                                     Left $ "expected all row entries to be unique in id and non-empty, got: " 
                                                                            ++ show (fst <$> list) ++ " for parent id " 
                                                                            ++ show ancestor2 ++ " for " ++ show offspring

                                                           mkTree (ancestor2's :: rest) generated
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

0 --Th
pedUnique : (0 p : Pedigree x) -> (0 p' : Pedigree x) -> p = p'
pedUnique Founder Founder = Refl
pedUnique Founder (Proband _ _) impossible
pedUnique (Proband _ _) Founder impossible
pedUnique (Proband ll lr) (Proband rl rr) 
 = let leq = pedUnique ll rl 
       req = pedUnique lr rr in
       rewrite leq in
       rewrite req in Refl 

total
name : (x : BinTree Name) -> {auto 0 px : Pedigree x} -> Name
name (Node _ n _) = n

total
id : (x : BinTree Name) -> {auto 0 px : Pedigree x} -> Int
id (Node _ n _) = n.id

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
        (x : BinTree Name)
     -> (y : BinTree Name) 
     -> {auto 0 px : Pedigree x}
     -> {auto 0 py : Pedigree y}
     -> Double
   kinship node1 node2
    = let rel = relationTy node1 node2 in
          case rel of
               Self self => assert_total 
                $ kinshipSelf self
               Nested off _ par => assert_total 
                $ kinshipNested off par
               Linear l r => assert_total 
                $ kinshipLinear l r
               
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
   isNested : -- x < y
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
        (x : BinTree Name) 
     -> {auto 0 p : Pedigree x} 
     -> Double
   kinshipSelf (Node (Node ll lx lr) name (Node rl rx rr)) {p = Proband _ _}
     = 0.5 * (1 + kinship (Node ll lx lr) (Node rl rx rr))
   kinshipSelf (Node Empty name Empty) {p = Founder} = 0.5
   
   total
   kinshipNested : 
        (x : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto prf : px =/= Founder {name = x.name} } 
     -> (y : BinTree Name)
     -> {auto 0 py : Pedigree y} 
     -> Double
   kinshipNested (Node (Node ll lx lr) _ (Node rl rx rr)) {px = Proband _ _} parent
    = 0.5 * (kinship (Node ll lx lr) parent + kinship (Node rl rx rr) parent)
   kinshipNested (Node Empty _ Empty) {px = Founder} _ = exFalso $ prf Refl 
  

   total
   kinshipLinear : 
        (x : BinTree Name) 
     -> (y : BinTree Name) 
     -> {auto 0 px : Pedigree x} 
     -> {auto 0 py : Pedigree y} 
     -> Double
   kinshipLinear (Node (Node a an a') name (Node b bn b')) (Node (Node c cn c') name' (Node d dn d')) {px = Proband _ _} {py = Proband _ _}
     = 0.25 * (  kinship (Node a an a') (Node c cn c') 
               + kinship (Node a an a') (Node d dn d') 
               + kinship (Node b bn b') (Node c cn c') 
               + kinship (Node b bn b') (Node d dn d'))
   kinshipLinear _ _ = 0

   data PkData : Type -> (0 p : BinTree Name) -> (0 q : BinTree Name) -> (0 y : BinTree Name) -> Type where
        MkPkData : (none : a) -> (one : a) -> (duplicated : a) -> (unique : a) -> PkData a p q y
   
   (Show a, Num a) => Show (PkData a x y z) where
      show (MkPkData zero one dup unique) = "{zero: " ++ show zero ++ ", one: " ++ show one ++ ", dup: " ++ show dup ++ ", unique: " ++ show unique ++ ", sum: " ++ show (zero + one + dup + unique) ++ "}"
    
   -- (Show a, Show b, Show c) => Show (x : a ** (y : b ** c)) where
   --    show (x ** (y ** z)) = "(" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ")"
   
   (+) : Num a => PkData a p q y -> PkData a p' q' y -> PkData a p'' q'' y
   (MkPkData x y z w) + (MkPkData x' y' z' w') = MkPkData (x + x') (y + y') (z + z') (w + w')
   
   (*) : Num a => a -> PkData a p q y -> PkData a p q y
   k * (MkPkData x y z w) = MkPkData (k * x) (k * y) (k * z) (k * w)

   total
   partialKinshipYY : Rat a => PkData a x x x 
   partialKinshipYY = MkPkData 0 0 (fromRational (1//2)) (fromRational (1//2))

   total
   partialKinshipFY : {name : _}
                   -> {0 a : _}
                   -> Num a
                   => let x = Node Empty name Empty in 
                               {y : _} 
                            -> {auto 0 px : Pedigree x} 
                            -> {auto 0 py : Pedigree y} 
                            -> {auto 0 prf : x =/= y} 
                            -> PkData a x y y
   partialKinshipFY = MkPkData 0 1 0 0

   total
   partialKinshipFF : Num a 
                   => {auto 0 px : Pedigree x} 
                   -> {auto 0 py : Pedigree y} 
                   -> {auto 0 pz : Pedigree z} 
                   -> {auto 0 prfs : (x =/= z, y =/= z)} 
                   -> PkData a x y z
   partialKinshipFF = MkPkData 1 0 0 0
   

   total
   contraposition : {f : a -> b} -> {x, y : a} -> f x =/= f y -> x =/= y -- theorem of classical logic, not derivable in intuitionistic logic
   contraposition _ = believe_me {a = () = ()} Refl

   total
   lemma : Element x px =/= Element y py -> x =/= y
   lemma = believe_me --TODO prove me later
   

   total
   apply : DecEq b => {auto inj : Injection (Subset a q) b} -> (x : a) -> (y : a) -> {auto 0 px : q x} -> {auto 0 py : q y} -> Dec (x = y)
   apply {inj = IsInjection f inj} x y
    = case decEq (f (Element x px)) (f (Element y py)) of
           No proof => No (lemma $ contraposition {f} proof)
           Yes proof => Yes (case inj _ _ proof of Refl => Refl)
   -- where
   --    lemma : Subset x p -> Subset y p -> Subset x p = Subset y p -> x = y
   --    lemma x y Refl = Refl

   total
   partialKinshipPY : Rat a
                   => (x : BinTree Name) 
                   -> (y : BinTree Name) 
                   -> {auto 0 px : Pedigree x}
                   -> {auto 0 py : Pedigree y} 
                   -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                   -> {auto 0  _ : x =/= y} 
                   -> PkData a x y y
   partialKinshipPY (Node (Node ll lx lr) _ (Node rl rx rr)) y {px = Proband _ _} 
      = assert_total $ 
        let left = case apply {inj} (Node ll lx lr) y of
                        No _ => partialKinshipPY {a} (Node ll lx lr) y
                        Yes Refl => partialKinshipYY
            right = case apply {inj} (Node rl rx rr) y of
                         No _ => partialKinshipPY {a} (Node rl rx rr) y
                         Yes Refl => partialKinshipYY
        in
            fromRational (1//2) * (left + right) 
   partialKinshipPY (Node Empty name Empty) y {px = Founder}
      = assert_total $ 
        case apply {inj} (Node Empty name Empty) y of
             No prf => partialKinshipFY {a} {prf}
             Yes Refl => partialKinshipYY
   partialKinshipPY Empty y impossible          
   partialKinshipPY (Node (Node _ _ _) _ Empty) y impossible
   partialKinshipPY (Node Empty _ (Node _ _ _)) y impossible
  
   total
   partialKinshipNested : Rat a
                       => (x : BinTree Name) 
                       -> (y : BinTree Name) 
                       -> (z : BinTree Name)
                       -> {auto 0 px : Pedigree x} 
                       -> {auto 0 py : Pedigree y} 
                       -> {auto 0 pz : Pedigree z} 
                       -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                       -> {auto 0 proofs : HList0 [x =/= y, x =/= z, y =/= z, px =/= Founder {name = x.name}]}
                       -> PkData a x y z
   partialKinshipNested (Node (Node ll lx lr) _ (Node rl rx rr)) y z {px = Proband _ _}
      = fromRational (1//2) * (partialKinship (Node ll lx lr) y z + partialKinship (Node rl rx rr) y z)
   partialKinshipNested _ _ _ {px = Founder} = let 0 notFounder = at 3 proofs in exFalso (notFounder Refl) --impossible

   total
   partialKinshipLinear : Rat a
                       => (x : BinTree Name)
                       -> (y : BinTree Name)
                       -> (z : BinTree Name)
                       -> {auto 0 px : Pedigree x}
                       -> {auto 0 py : Pedigree y}
                       -> {auto 0 pz : Pedigree z}
                       -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                       -> {auto 0 proofs : HList0 [x =/= y, x =/= z, y =/= z]}
                       -> PkData a x y z
   partialKinshipLinear (Node (Node a an a') _ (Node b bn b')) (Node (Node c cn c') _ (Node d dn d')) {px = Proband _ _} {py = Proband _ _} z
     = fromRational (1//4) * (+)((+)  
                    (partialKinship (Node a an a') (Node c cn c') z)
                    (partialKinship (Node a an a') (Node d dn d') z))
                  ((+) 
                    (partialKinship (Node b bn b') (Node c cn c') z)
                    (partialKinship (Node b bn b') (Node d dn d') z)) {p = Node a an a'} {p' = Node b bn b'} {q = Node c cn c'} {q' = Node d dn d'}
   partialKinshipLinear (Node (Node ll lx lr) _ (Node rl rx rr)) a {px = Proband _ _} z
    = fromRational (1//2) * (partialKinship (Node ll lx lr) a z + partialKinship (Node rl rx rr) a z)
   partialKinshipLinear a (Node (Node ll lx lr) _ (Node rl rx rr)) {py = Proband _ _} z
    = fromRational (1//2) * (partialKinship (Node ll lx lr) a z + partialKinship (Node rl rx rr) a z)
   partialKinshipLinear (Node Empty x Empty) (Node Empty y Empty) z {px = Founder} {py = Founder} 
    = partialKinshipFF 
   partialKinshipLinear (Node Empty _ (Node _ _ _)) (Node Empty _ (Node _ _ _)) z impossible
   
   total
   partialKinshipSelf : Rat a
                     => (x : BinTree Name)   
                     -> (z : BinTree Name)
                     -> {auto 0 px : Pedigree x}
                     -> {auto 0 pz : Pedigree z}
                     -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                     -> {auto 0 proofs : x =/= z}
                     -> PkData a x x z
   partialKinshipSelf (Node (Node ll lx lr) _ (Node rl rx rr)) z {px = Proband _ _}
    = let (MkPkData zero one dup unique) = partialKinship (Node ll lx lr) (Node rl rx rr) z
          zero' = zero + fromRational (1//4) * one
          one' = fromRational (1//2) * one
          dup' = fromRational (1//4) * one + dup + fromRational (1//2) * unique
          unique' = fromRational (1//2) * unique
      in    
          MkPkData zero' one' dup' unique'
   partialKinshipSelf (Node Empty x Empty) z {px = Founder}
    = partialKinshipFF
   
   total
   partialKinshipCommutative : PkData a x y z -> PkData a y x z --not actually a formal proof
   partialKinshipCommutative (MkPkData a b c d) = MkPkData a b c d

   total
   partialKinship : Rat a
                 => (x : BinTree Name) 
                 -> (y : BinTree Name) 
                 -> (z : BinTree Name)
                 -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                 -> {auto 0 px : Pedigree x} 
                 -> {auto 0 py : Pedigree y} 
                 -> {auto 0 pz : Pedigree z}
                 -> PkData a x y z
   partialKinship x y z
    = assert_total $ 
      case apply {inj} x y of
           Yes Refl => case apply {inj} {px} {py = pz} x z of
                            Yes Refl => partialKinshipYY
                            No contra => partialKinshipSelf {px} x z
           No xNotY => case (apply {inj} x z, apply {inj} y z) of
                             (Yes Refl, Yes Refl) => exFalso (xNotY Refl) -- impossible
                             (Yes Refl, No _) => partialKinshipCommutative (partialKinshipPY {py = px} y z)
                             (_, Yes Refl) => partialKinshipPY {py} x z
                             (No xNotZ, No yNotZ) 
                              => case isNested x y of
                                      (True ** xNotFounder) => partialKinshipNested x y z
                                      (False ** ()) => case isNested y x of
                                                            (True ** yNotFounder) => partialKinshipCommutative (partialKinshipNested {proofs = [symNot xNotY, yNotZ, xNotZ, yNotFounder]} y x z)
                                                            (False ** ()) => partialKinshipLinear x y z
     
   total
   partialKinship' : Rat a
                  => (x : BinTree Name)
                  -> (z : BinTree Name)
                  -> {auto inj : Injection (Subset (BinTree Name) Pedigree) Int} 
                  -> {auto 0 px : Pedigree x}
                  -> {auto 0 pz : Pedigree z}
                  -> Maybe (l ** (r ** PkData a l r z))
   partialKinship' (Node (Node ll lx lr) _ (Node rl rx rr)) z {px = Proband _ _}
    = assert_total $ Just ( _ ** (_ ** partialKinship (Node ll lx lr) (Node rl rx rr) z))
   partialKinship' (Node Empty _ Empty) z {px = Founder} = Nothing



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

Eq Allele where
   ALeft == ALeft = True
   ARight == ARight = True
   AOther == AOther = True
   _ == _ = False

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

destroy : (1 _ : LinArray a) -> ()
destroy x = let () = destroyInt $ size x in ()
  where
     destroyInt : (1 _ : Int) -> ()
     destroyInt = believe_me (\x : Int => ()) --TODO THIS IS SUPER HACKY

total        
simulateAllelePropagation : --simulate allele propagation towards X, accounting only for Y's alleles
      (x : BinTree Name)
   -> (y : BinTree Name)
   -> {auto 0 px : Pedigree x}
   -> {auto 0 py : Pedigree y}
   -> (1 arr : LinArray (Maybe (Vect 2 Allele)))
   -> L IO {use = 1} (LPair (Vect 2 Allele) (LinArray (Maybe (Vect 2 Allele))))
simulateAllelePropagation (Node (Node ll lx lr) x (Node rl rx rr)) y {px = Proband _ _} pr
 = case mread pr (TableRow.id x) of
        (Just Nothing # pr) 
                => case x == y.name of
                        True => pure1 ([ALeft, ARight] # pr)
                        False => do
                             (l # pr) <- assert_total $ simulateAllelePropagation (Node ll lx lr) y pr
                             left <- select2' l
                             (r # pr) <- assert_total $ simulateAllelePropagation (Node rl rx rr) y pr
                             right <- select2' r
                             let 1 pr = write pr (TableRow.id x) (Just [left, right])
                             pure1 ([ left
                                  , right] # pr)    
        ((Just $ Just xx) # pr) => pure1 (xx # pr)
        (Nothing # ar) => let () = destroy ar in assert_total $ idris_crash "index out of bounds"
simulateAllelePropagation (Node _ x _) y {px = Founder} pr
 = case x == y.name of
        True => pure1 ([ALeft, ARight] # pr)
        False => pure1 ([AOther, AOther] # pr)

initArray : (1 ar : LinArray a) -> Int -> a -> LinArray a
initArray ar i x = 
 let (size # ar) = msize ar in
     if i >= size then ar
                  else let ar = write ar i x in
                           assert_total $ initArray ar (i + 1) x

         
total
simulate : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> (target : Vect 2 Allele -> a)
   -> IO a
simulate x y nodeCount target = 
   do
      res <- run $ newArray nodeCount $ \ar =>  
                    do   
                       let ar = initArray ar 0 Nothing   
                       (s # ar) <- simulateAllelePropagation x y ar
                       let () = destroy ar
                       pure $ target s
      pure res   

total
simulateBqOnce : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> IO Double
simulateBqOnce x y nodeCount = simulate x y nodeCount ((0.5 *) . cast {to = Double} . count)

total
simulateZero : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> IO Bool
simulateZero x y nodeCount = simulate x y nodeCount (== [AOther, AOther])

total
simulateOne : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> IO Bool
simulateOne x y nodeCount = simulate x y nodeCount (\x => x == [AOther, ALeft] || x == [AOther, ARight] || x == [ALeft, AOther] || x == [ARight, AOther])

total
simulateDup : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> IO Bool
simulateDup x y nodeCount = simulate x y nodeCount (\x => x == [ALeft, ALeft] || x == [ARight, ARight])

total
simulateUnique : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> IO Bool
simulateUnique x y nodeCount = simulate x y nodeCount (\x => x == [ALeft, ARight] || x == [ARight, ALeft])

total
addToBin : Vect 4 Int -> Vect 2 Allele -> Vect 4 Int
addToBin [a, b, c, d] [AOther, AOther] = [a + 1, b, c, d]
addToBin [a, b, c, d] [AOther, ALeft] = [a, b + 1, c, d]
addToBin [a, b, c, d] [AOther, ARight] = [a, b + 1, c, d]
addToBin [a, b, c, d] [ALeft, AOther] = [a, b + 1, c, d]
addToBin [a, b, c, d] [ALeft, ALeft] = [a, b, c + 1, d]
addToBin [a, b, c, d] [ALeft, ARight] = [a, b, c, d + 1]
addToBin [a, b, c, d] [ARight, AOther] = [a, b + 1, c, d]
addToBin [a, b, c, d] [ARight, ALeft] = [a, b, c, d + 1]
addToBin [a, b, c, d] [ARight, ARight] = [a, b, c + 1, d]

total
simulatePk : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> (i : Nat)
   -> Vect 4 Int
   -> IO (Vect 4 Int)
simulatePk x y nodeCount (S i) bin
 = do gene <- simulate x y nodeCount (\x => x)
      simulatePk x y nodeCount i (addToBin bin gene)
simulatePk _ _ _ 0 bin = pure bin      

total
simulateBq : 
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> (i : Nat)
   -> Double
   -> IO Double
simulateBq x y nodeCount (S i) sum
 = do bq <- simulateBqOnce x y nodeCount
      simulateBq x y nodeCount i (sum + bq)
simulateBq _ _ _ 0 sum = pure sum  

total
simulatePk' :
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> (n : Nat)
   -> IO (Vect 4 Double)
simulatePk' x y nodeCount n
 = do bin <- simulatePk x y nodeCount n [0, 0, 0, 0]
      pure (map ( ( / n.cast) . cast {to = Double}) bin)
      

total
simulateBq' :
      (x : BinTree Name) 
   -> {auto 0 px : Pedigree x} 
   -> (y : BinTree Name) 
   -> {auto 0 py : Pedigree y}
   -> (nodeCount : Int)
   -> (n : Nat)
   -> IO Double
simulateBq' x y nodeCount n
 = do sum <- simulateBq x y nodeCount n 0
      pure (sum / n.cast)
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

indexedFounders : (x : BinTree Name) -> List (Int, BinTree Name) -> {auto 0 px : Pedigree x} -> Maybe (List (Int, BinTree Name))
indexedFounders x all
 = let fo_ids : List Int = TableRow.id <$> SortedSet.toList (founders x)
       fo_in = fmapSnd ((flip lookup) all) . dup <$> fo_ids
   in  sequence fo_in    


contains : Set a -> a -> Bool
contains = flip SortedSet.contains
%hide SortedSet.contains
%hide Data.List.toList



byId : List Int -> Name -> Bool
byId list n = isJust $ List.find (== TableRow.id n) list 

showPk : (Show a, Num a) => (x ** (y ** PkData a x y z)) -> String
showPk (_ ** (_ ** pk)) = show pk

toBq : Rat a => (x ** (y ** PkData a x y z)) -> a
toBq (_ ** (_ ** MkPkData zero one dup unique)) = fromRational (1//2) * (one + dup + 2 * unique)


testRat : IO ()
testRat = do
   let a = 0//4
   let b = 8//1
   let c = (Rational.(*) a b)
   printLn c

main1 : IO ()
main1 = testRat


dependent : forall p. ((x : a) -> p x) -> (x : a) -> (x ** p x)
dependent f x = (x ** f x)

idIsInjection : Injection (Subset (BinTree Name) Pedigree) Int
idIsInjection = IsInjection (\(Element x px) => x.id) (\_, _, _ => believe_me {a = () = ()} Refl)

ks : Rat a => SortedMap Int (BinTree Name) -> List Int -> Int -> Int -> Maybe a
ks trees founders i1 i2
 = case (lookup i1 trees, lookup i2 trees, sequence ((flip lookup) trees <$> founders)) of
        (Just t1, Just t2, Just founders)
          => case (asPedigree t1, asPedigree t2, sequenceDep (dependent asPedigree <$> founders)) of
                  (Just p1, Just p2, Just tps)
                    => let pks = map (\(fo ** foPed) => let (MkPkData _ _ dup _) = partialKinship {a} {inj = idIsInjection} t1 t2 fo 
                                                         in trace (show $ "founder " ++ show fo.id) dup) tps
                           sum = foldl (+) 0 pks
                       in    
                           Just sum
                  _ => Nothing   
        _ => Nothing
where
   sequenceDep : forall a. {p : a -> Type} -> List (x ** Maybe (p x)) -> Maybe (List (x ** p x))
   sequenceDep Nil = Just Nil
   sequenceDep ((x ** Just px) :: xs) = ((x ** px) ::) <$> sequenceDep xs
   sequenceDep ((_ ** Nothing) :: _) = Nothing



toArray : List a -> IArray a
toArray list = toIArray (newArray (cast $ length list) (helper list 0)) id
where
   id : forall a. a -> a 
   id x = x
    
   helper : forall a. List a -> Nat -> (1 _ : LinArray a) -> LinArray a
   helper [] _ ar = ar
   helper (x :: xs) i ar = let ar = write ar (cast i) x
                           in  helper xs (S i) ar

arrayToList : IArray a -> List a
arrayToList ar = let s = size ar in
                     helper (intToNat s) [] ar
where
  helper : forall a. Nat -> List a -> IArray a -> List a
  helper (S i) list ar = case read ar (cast i) of
                              Nothing => assert_total $ idris_crash "impossible"
                              (Just x) => helper i (x :: list) ar
  helper 0 list _ = list


getWithDefault : BinTree a -> Lazy a -> a
getWithDefault Empty x = x
getWithDefault (Node _ x _) _ = x

main : IO ()
main = let (>>=) = io_bind in 
   do
      args <- getArgs
      putStrLn (show args)
      let [_, filename] = args
             | _ => do putStrLn "no filename argument"
                       exitFailure
      str <- readFile filename >>= orFail
      let tagged@[nt1, nt2] = the (Vect _ Int) [0, 4]
      trees <- pure (parseTreeCsv str) >>= orFail
      let Just (mainId, main) = trees.head'
            | _ => do putStrLn "Empty tree"
                      exitFailure
      let (Just pmain) = asPedigree main
            | _ => do putStrLn "main is not pedigree"; exitFailure
      putStrLn $ "Depth: " ++ show main.maxDepth
      let (maxLen, maxPath) = showMaxPath (\x => fixedWidth (show x.id) 4 AlignLeft ++ " " ++ x.name) main
      putStrLn $ "Max depth: " ++ show maxLen
      putStrLn $ "Num Id   Name\n" ++ unlines ((\(p, i) => fixedWidth (show i) 3 AlignLeft ++ " " ++ p) <$> zip (lines maxPath) [1..maxLen])
      putStrLn $ "Node count: " ++ show trees.length
      putStrLn $ "Main name: " ++ main.name.name
      let (Just t1, Just t2) = (lookup nt1 trees, lookup nt2 trees)
            | _ => do putStrLn "Tagged trees not found"; exitFailure
      let (Just p1, Just p2) = (asPedigree t1, asPedigree t2)
            | _ => do putStrLn "Tagged trees are not pedigrees"; exitFailure
      let fo = main.founders
      let fo_list = fo.toList
      let fo_ids = TableRow.id <$> fo_list
      let t1_ids = TableRow.id <$> (founders t1).toList
      let t2_ids = TableRow.id <$> (founders t2).toList
      putStrLn $ "number of founders: " ++ show (fo_list.length)
      putStrLn $ "founder ids: " ++ show fo_ids
      putStrLn $ "t1 number of founders: " ++ show (t1_ids.length)
      putStrLn $ "t2 number of founders: " ++ show (t2_ids.length)
      putStrLn $ show (t1.name, t2.name)
      putStrLn $ "Kinship: " ++ show (kinship t1 t2)
      -- let (Just founderTrees) = indexedFounders main trees
      --     | _ => do putStrLn $ "Bad founder ids"; exitFailure
          
      let pks = partialKinship' {a = Double} {inj = idIsInjection} t1 t2
      putStrLn $ "Partial kinship " ++ show (showPk <$> pks)
      -- below we assume that in csv file rows are ordered by ascending id, min id = 1
      let sortedTrees = sortBy (curry $ uncurry compare . (\(x, y) => (fst x, fst y))) trees
      putStrLn $ "num of names " ++ show (length trees)
      let findMissing = foldl (\(missing, x), y => if x + 1 /= y then ([x + 1..y-1] ++ missing, y) else (missing, y)) (the (List Int) [], the Int 0) (Builtin.fst <$> sortedTrees)
      pure ()
      putStrLn $ show findMissing

      let treesMap = SortedMap.fromList sortedTrees
      putStrLn $ "Kinship V2: " ++ show (ks {a = Double} treesMap fo_ids nt1 nt2)
      putStrLn $ "Blood Quota " ++ show (toBq <$> pks)
      srand' !timeMillis
      simPk <- simulatePk' t1 t2 (trees.length.cast + 1) 100000
      putStrLn $ "Sim Partial kinship: " ++ show simPk
      --simBq <- simulateBq' t1 t2 (trees.length.cast + 1) 10000
      --putStrLn $ "Sim Blood Quota: " ++ show simBq
      -- bqss <- sequence $ List.replicate 10000 $ simulateBq t1 t2 (trees.length.cast + 1) 
      -- let mean = foldl (+) 0 bqss / bqss.length.cast{to=Double}
      -- let minv = foldl min 1 bqss
      -- let maxv = foldl max 0 bqss
      -- putStrLn $ "min: " ++ show minv ++ ", max: " ++ show maxv
      -- let variance = sqrt $ foldl (\l, r => l + (r - mean) * (r - mean)) 0 bqss / (bqss.length.cast{to=Double} - 1)
      -- putStrLn $ "bloodQuota simulated mean: " ++ show mean
      -- putStrLn $ "variance: " ++ show variance


