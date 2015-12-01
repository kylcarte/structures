{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Data.Structure where

import Data.Type.Product (Prod(..))
import qualified Data.Type.Product as P
import Data.Type.Sum (Sum(..))
import qualified Data.Type.Sum as S
import Data.Type.Conjunction
import Data.Type.Quantifier (Some(..),some)
import Data.Type.Index
import Data.Type.Length
import Type.Class.HFunctor
import Type.Class.Known
import Type.Family.List
import Type.Family.Monoid
import Data.Type.Option
import Control.Applicative
import Control.Monad
import Text.Read
import Data.Char
import Data.Maybe

data S (str :: (k -> *) -> l -> *) (p :: l -> k -> *) :: (k -> *) -> k -> * where
  (:$) :: !(p b a)
       -> !(str rec b)
       -> S str p rec a
infix 1 :$

instance HFunctor str => HFunctor (S str p) where
  map' f (p :$ s) = p :$ map' f s

mapStr ::
     (forall x. str rec x -> str' rec' x)
  -> S str  p rec a
  -> S str' p rec' a
mapStr f (p :$ s) = p :$ f s

traverseStr :: Applicative f
  => (forall x. str rec x -> f (str' rec' x))
  -> S str  p rec a
  -> f (S str' p rec' a)
traverseStr f (p :$ s) = (p :$) <$> f s

mapRec ::
     (forall x. (forall y. rec y -> rec' y) -> str rec x -> str' rec' x)
  -> (forall x. rec x -> rec' x)
  -> S str  p rec  a
  -> S str' p rec' a
mapRec g f = mapStr $ g f

traverseRec :: Applicative f
  => (forall x. (forall y. rec y -> f (rec' y)) -> str rec x -> f (str' rec' x))
  -> (forall x. rec x -> f (rec' x))
  -> S str  p rec  a
  -> f (S str' p rec' a)
traverseRec g f = traverseStr $ g f

newtype Structure str p a = Structure
  { viewStructure :: S str p (Structure str p) a
  }

mapStructure :: HFunctor str
  => (forall x. str (Structure str' p) x -> str' (Structure str' p) x)
  -> Structure str  p a
  -> Structure str' p a
mapStructure f = Structure . mapStr (f . map' (mapStructure f)) . viewStructure

mapStructureM :: (HTraversable str, Monad f)
  => (forall x. str (Structure str' p) x -> f (str' (Structure str' p) x))
  -> Structure str  p a
  -> f (Structure str' p a)
mapStructureM f = fmap Structure . traverseStr (f <=< traverse' (mapStructureM f)) . viewStructure

mapSig :: HFunctor str
  => (forall y x. p y x -> str (Structure str' q) y -> S str' q (Structure str' q) x)
  -> Structure str  p a
  -> Structure str' q a
mapSig f (Structure (p :$ s)) = Structure $ f p $ map' (mapSig f) s

mapSigM :: (HTraversable str, Monad f)
  => (forall y x. p y x -> str (Structure str' q) y -> f (S str' q (Structure str' q) x))
  -> Structure str  p a
  -> f (Structure str' q a)
mapSigM f (Structure (p :$ s)) = fmap Structure $ f p =<< traverse' (mapSigM f) s

lmapSig :: HFunctor str
  => (forall rec y x. p y x -> str rec y -> S str' q rec x)
  -> Structure str  p a
  -> Structure str' q a
lmapSig f (Structure (p :$ s)) = Structure $ f p $ map' (mapSig f) s

type Tree = Structure Prod
type Path = Structure Sum

struct :: p b a -> str (Structure str p) b -> Structure str p a
struct p s = Structure $ p :$ s

($$) :: p b a -> str (Structure str p) b -> Structure str p a
($$) = struct
infixl 2 $$

data Syntax :: [*] -> * -> * where
  Int  :: Int
       -> Syntax '[] Int
  Bool :: Bool
       -> Syntax '[] Bool
  Op   :: (Int -> Int -> Int)
       -> Syntax '[Int,Int] Int
  Test :: (Int -> Bool)
       -> Syntax '[Int] Bool
  If   :: Syntax '[Bool,a,a] a

type Exp  = Tree Syntax
type Node = Path Syntax

class Arguments (f :: k -> *) (as :: k) (r :: *) (args :: *) | f as args -> r where
  withArgs :: (f as -> r) -> args

instance (Known Length as, s ~ ProdArgs f as r) => Arguments (Prod f) as r s where
  withArgs f = go f (known :: Length as)
    where
    go :: (Prod f xs -> r) -> Length xs -> ProdArgs f xs r
    go f = \case
      LZ   -> f Ø
      LS l -> \a -> go (f . (a :<)) l

type family ProdArgs (f :: k -> *) (as :: [k]) (r :: *) :: * where
  ProdArgs f Ø         r = r
  ProdArgs f (a :< as) r = f a -> ProdArgs f as r

node :: forall p as a. Known Length as => p as a -> ProdArgs (Tree p) as (Tree p a)
node p = withArgs (Structure . (p :$) :: Prod (Tree p) as -> Tree p a)

instance Arguments (Sum f) as r (Index as a -> f a -> r) where
  withArgs f i a = f $ S.injectSum i a

-- (@!) :: forall p as a b. p as b -> Index as a -> Path p a -> Path p b
-- (@!) p = withArgs (Structure . (p :$) :: Sum (Path p) as -> Path p b)

newtype (.:.) (f :: (l -> *) -> m -> *) (g :: (k -> *) -> l -> *) :: (k -> *) -> m -> * where
  HComp :: { getHComp :: f (g h) a }
        -> (f .:. g) h a
infixr 8 .:.

instance (HFunctor f, HFunctor g) => HFunctor (f .:. g) where
  map' f = HComp . map' (map' f) . getHComp

instance (HFoldable f, HFoldable g) => HFoldable (f .:. g) where
  foldMap' f = foldMap' (foldMap' f) . getHComp

instance (HTraversable f, HTraversable g) => HTraversable (f .:. g) where
  traverse' f = fmap HComp . traverse' (traverse' f) . getHComp

type Grad v u t = Tree (Gradual v u t)

data Gradual (v :: *) (u :: k -> *) (t :: l -> k -> *) :: l -> k -> * where
  Full :: t b a -> Gradual v u t b a
  Part :: u a   -> Gradual v u t b a
  Hole :: v     -> Gradual v u t b a

{-
type Grad v t = Structure (Option .:. Prod) (Gradual v t)

data Gradual (v :: *) (t :: l -> k -> *) :: Maybe l -> k -> * where
  Full :: t b a -> Gradual v t (Just b) a
  Hole :: v     -> Gradual v t Nothing  a
-}

full :: t b a -> Prod (Grad v u t) b -> Grad v u t a
full = struct . Full

full_ :: t Ø a -> Grad v u t a
full_ = ($ Ø) . full

part :: u a -> Prod (Grad v u t) b -> Grad v u t a
part = struct . Part

part_ :: u a -> Grad v u t a
part_ = ($ Ø) . part

hole :: v -> Prod (Grad v u t) b -> Grad v u t a
hole = struct . Hole

hole_ :: v -> Grad v u t a
hole_ = ($ Ø) . hole

type GExp = Grad String E Syntax

data E a
  = I Int
  | B Bool
  | O (Int -> Int -> Int) (E Int) (E Int)
  | T (Int -> Bool) (E Int)
  | C (E Bool) (E a) (E a)

instance Show (E a) where
  showsPrec d e = showParen (d > 0) $ case e of
    I i     -> showString "I " . shows i
    B b     -> showString "B " . shows b
    O _ x y -> showString "O "
             . showsPrec 11 x
             . showChar ' '
             . showsPrec 11 y
    T _ x   -> showString "T "
             . showsPrec 11 x
    C t c a -> showString "C "
             . showsPrec 11 t
             . showChar ' '
             . showsPrec 11 c
             . showChar ' '
             . showsPrec 11 a

instance Read (E a) where
  readsPrec d s = concat
    [ readInt s
    , readBool s
    , readOp   d 6 7 7 "+" (+) s
    , readOp   d 6 7 7 "-" (-) s
    , readOp   d 7 8 8 "*" (*) s
    , readTest d "zero" (== 0) s
    , readTest d "odd"  odd s
    , readTest d "even" even s
    , readIf   d s
    ]

readInt :: ReadS (E a)
readInt s0 =
  [ (I $ read n,s1)
  | (n,s1) <- lex s0
  , all isDigit n
  ]

readBool :: ReadS (E a)
readBool s0 =
  [ (B True,s1)
  | ("True",s1) <- lex s0
  ] ++
  [ (B False,s1)
  | ("False",s1) <- lex s0
  ]

readOp :: Int -> Int -> Int -> Int -> String -> (Int -> Int -> Int) -> ReadS (E a)
readOp d pr l r op f = readParen (d > pr) $ \s0 ->
  [ (O f x y,s3)
  | (x,s1) <- readsPrec l s0
  , (o,s2) <- lex s1
  , o == op
  , (y,s3) <- readsPrec r s2
  ]

readTest :: Int -> String -> (Int -> Bool) -> ReadS (E a)
readTest d tst f = readParen (d > 0) $ \s0 ->
  [ (T f x,s2)
  | (t,s1) <- lex s0
  , t == tst
  , (x,s2) <- readsPrec 11 s1
  ]

readIf :: Read (E a) => Int -> ReadS (E a)
readIf d = readParen (d > 0) $ \s0 ->
  [ (C t c a,s6)
  | ("if",s1) <- lex s0
  , (t,s2) <- readsPrec 0 s1
  , ("then",s3) <- lex s2
  , (c,s4) <- readsPrec 0 s3
  , ("else",s5) <- lex s4
  , (a,s6) <- readsPrec 0 s5
  ]

readE :: Read (E a) => String -> Maybe (E a)
readE = readMaybe

g0 :: GExp Int
g0 = full_ (Int 2)

g1 :: GExp Int
g1 = hole_ "3"

g2 :: Maybe (GExp Int)
g2 = mapSigM
  ( curry $ \case
    (Full t,args) -> Just $ Full t :$ args
  ) g1

checkInt :: GExp a -> Maybe (Exp Int)
checkInt e = case viewStructure e of
  Full p :$ s -> case (p,s) of
    (Int i,_)  -> return $ int i
    (Bool{},_) -> Nothing
    (Op f,x :< y :< Ø) -> do
      a <- checkInt x
      b <- checkInt y
      return $ op f a b
    (Test{},_) -> Nothing
    (If,x :< y :< z :< Ø) -> do
      a <- checkBool x
      b <- checkInt y
      c <- checkInt z
      return $ cond a b c
  Part e :$ s -> _

checkBool :: GExp a -> Maybe (Exp Bool)
checkBool = undefined

parseE :: E a -> Maybe (Some GExp)
parseE e = Some <$> parseInt  e
       <|> Some <$> parseBool e

parseInt :: E a -> Maybe (GExp Int)
parseInt = \case
  I i     -> Just $ full_ $ Int i
  B b     -> Nothing
  O f x y -> do
    a <- parseInt x
    b <- parseInt y
    return $ full (Op f) $ a :< b :< Ø
  T f x   -> Nothing
  C t c a -> do
    b <- parseBool t
    d <- parseInt c
    e <- parseInt a
    return $ full If $ b :< d :< e :< Ø

parseBool :: E a -> Maybe (GExp Bool)
parseBool = \case
  I i     -> Nothing
  B b     -> Just $ full_ $ Bool b
  O f x y -> Nothing
  T f x   -> do
    a <- parseInt x
    return $ full (Test f) $ a :< Ø
  C t c a -> do
    b <- parseBool t
    d <- parseBool c
    e <- parseBool a
    return $ full If $ b :< d :< e :< Ø

{-
p0 :: Node Int
p0 = Structure $ Int 0 :$ _
-}

{-
inOp :: (Int -> Int -> Int) -> Index '[Int,Int] Int -> Node Int -> Node Int
inOp o i = Op o @! i

inTest :: (Int -> Bool) -> Node Int -> Node Bool
inTest t = Test t @! IZ

inIf :: Index '[Bool,a,a] b -> Node b -> Node a
inIf i = If @! i
-}

int :: Int -> Exp Int
int = node . Int

bool :: Bool -> Exp Bool
bool = node . Bool

op :: (Int -> Int -> Int) -> Exp Int -> Exp Int -> Exp Int
op = node . Op

(.+),(.-),(.*) :: Exp Int -> Exp Int -> Exp Int
(.+) = op (+)
(.-) = op (-)
(.*) = op (*)
infixl 7 .*
infixl 6 .+
infixl 6 .-

cond :: Exp Bool -> Exp a -> Exp a -> Exp a
cond = node If

