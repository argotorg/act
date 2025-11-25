{-# Language GADTs #-}
{-# Language LambdaCase #-}
{-# Language DataKinds #-}

module Act.Print where

import Prelude hiding (GT, LT)
import Data.ByteString.UTF8 (toString)
import Prettyprinter hiding (brackets)
import qualified Prettyprinter.Render.Terminal as Term
import qualified Data.Text as Text

import System.IO (stdout)
import Data.Text qualified as T
import EVM.ABI (abiTypeSolidity)

import Data.List
import Data.Bifunctor

import Act.Syntax.Typed hiding (annotate)


prettyAct :: Act t -> String
prettyAct (Act _ contracts)
  = unlines (fmap prettyContract contracts)

prettyContract :: Contract t -> String
prettyContract (Contract ctor behvs) = unlines $ intersperse "\n" $ (prettyCtor ctor):(fmap prettyBehaviour behvs)

prettyCtor :: Constructor t -> String
prettyCtor (Constructor name interface pres cases posts invs)
  =   "constructor of " <> name
  >-< "interface " <> show interface
  <> prettyPre pres
  <> prettyCreates cases
  <> prettyPost posts
  <> prettyInvs invs
  where
    prettyCreates [] = ""
    prettyCreates cs = header "creates" >-< block (concatMap (\(cond, updates) -> prettyExp cond : map prettyUpdate' updates) cs)

    prettyInvs [] = ""
    prettyInvs _ = error "TODO: pretty print invariants"

    prettyUpdate' :: StorageUpdate t -> String
    prettyUpdate' (Update v r e) = prettyTValueType v <> " " <> prettyRef r <> " := " <> prettyExp e
    
    prettyTValueType :: TValueType a -> String
    prettyTValueType (TContract n) = n
    prettyTValueType t = T.unpack (abiTypeSolidity (toAbiType t))

prettyValueType :: ValueType -> String
prettyValueType = \case
  ValueType (TContract n) -> n
  ValueType t -> T.unpack (abiTypeSolidity (toAbiType t))


prettyBehaviour :: Behaviour t -> String
prettyBehaviour (Behaviour name contract interface preconditions cases postconditions)
  =   "behaviour " <> name <> " of " <> contract
  >-< "interface " <> (show interface)
  <> prettyPre preconditions
  <> prettyCases' cases
  <> prettyPost postconditions
  where
    prettyCases' [] = ""
    prettyCases' cs = header "cases" >-< block (concatMap prettyCase cs)
    
    prettyCase (cond, (updates, mret)) = 
      [prettyExp cond <> ":"] 
      ++ map (("  " <>) . prettyUpdate) updates
      ++ maybe [] (\ret -> ["  returns " <> prettyTypedExp ret]) mret



prettyPre :: [Exp ABoolean t] -> String
prettyPre [] = ""
prettyPre p = header "iff" >-< block (prettyExp <$> p)

prettyPost :: [Exp ABoolean t] -> String
prettyPost [] = ""
prettyPost p = header "ensures" >-< block (prettyExp <$> p)

header :: String -> String
header s = "\n\n" <> s <> "\n"

block :: [String] -> String
block l = "  " <> intercalate "\n  " l

(>-<) :: String -> String -> String
x >-< y = x <> "\n" <> y

prettyExp :: Exp a t -> String
prettyExp e = case e of

  -- booleans
  Or _ a b -> print2 "or" a b
  Eq _ _ a b -> print2 "==" a b
  LT _ a b -> print2 "<" a b
  GT _ a b -> print2 ">" a b
  LEQ _ a b -> print2 "<=" a b
  GEQ _ a b -> print2 ">=" a b
  And _ a b -> print2 "and" a b
  NEq _ _ a b -> print2 "=/=" a b
  Neg _ a -> "(not " <> prettyExp a <> ")"
  Impl _ a b -> print2 "=>" a b
  LitBool _ b -> if b then "true" else "false"

  -- integers
  Add _ a b -> print2 "+" a b
  Sub _ a b -> print2 "-" a b
  Mul _ a b -> print2 "*" a b
  Div _ a b -> print2 "/" a b
  Mod _ a b -> print2 "%" a b
  Exp _ a b -> print2 "^" a b
  UIntMax _ a -> show $ uintmax a
  UIntMin _ a -> show $ uintmin a
  IntMax _ a -> show $ intmax a
  IntMin _ a -> show $ intmin a
  InRange _ a b -> "inRange(" <> show a <> ", " <> prettyExp b <> ")"
  LitInt _ a -> show a
  IntEnv _ a -> prettyEnv a

  -- bytestrings
  Cat _ a b -> print2 "++" a b
  Slice _ a b c -> (prettyExp a) <> "[" <> (prettyExp b) <> ":" <> (prettyExp c) <> "]"
  ByStr _ a -> a
  ByLit _ a -> toString a
  ByEnv _ a -> prettyEnv a

  Array _ [] -> "[]"
  Array _ l ->
    "[" <> (intercalate "," $ fmap prettyExp l) <> "]"

  -- contracts
  Create _ f ixs _ -> f <> "(" <> (intercalate "," $ fmap prettyTypedExp ixs) <> ")"

  --polymorphic
  ITE _ a b c -> "(if " <> prettyExp a <> " then " <> prettyExp b <> " else " <> prettyExp c <> ")"
  VarRef _ _ SStorage r -> timeParens (getTime r) $ prettyRef r
  VarRef _ _ SCalldata r -> prettyRef r
  Address _ c  -> prettyExp c
  Mapping _ _ _ kvs -> "mapping(" <> intercalate ", " (map (\(k,v) -> prettyExp k <> " => " <> prettyExp v) kvs) <> ")"
  MappingUpd _ r _ _ kvs -> prettyRef r <> "{" <> intercalate ", " (map (\(k,v) -> prettyExp k <> " => " <> prettyExp v) kvs) <> "}"
  where
    print2 sym a b = "(" <> prettyExp a <> " " <> sym <> " " <> prettyExp b <> ")"
    getTime :: Ref Storage t -> Time t
    getTime (SVar _ t _ _) = t
    getTime (RArrIdx _ r _ _) = getTime r
    getTime (RMapIdx _ r _ _) = getTime r  
    getTime (RField _ r _ _) = getTime r

prettyTypedExp :: TypedExp t -> String
prettyTypedExp (TExp _ e) = prettyExp e

prettyRef :: Ref k t -> String
prettyRef = \case
  CVar _ _ n -> n
  SVar _ _ _ n -> n
  RArrIdx _ r _ args -> prettyRef r <> concatMap (brackets . prettyTypedExp . fst) args
  RMapIdx _ r _ args -> prettyRef r <> concatMap (brackets . prettyTypedExp) args
  RField _ r _ n -> prettyRef r <> "." <> n
  where
    brackets str = "[" <> str <> "]"

prettyUpdate :: StorageUpdate t -> String
prettyUpdate (Update _ r e) = prettyRef r <> " => " <> prettyExp e

prettyEnv :: EthEnv -> String
prettyEnv e = case e of
  Caller -> "CALLER"
  Callvalue -> "CALLVALUE"
  Origin -> "ORIGIN"
  This -> "THIS"

-- | Invariant predicates are represented internally as a pair of timed
-- expressions, one over the prestate and one over the poststate.  This is good
-- since it keeps untimed expressions away from the various backends, and
-- maintains a nice seperation between the various compilation passes, but
-- unfortunately requires us to strip the timing out if we want to print the
-- invariant in a way that is easily digestible by humans, requiring a less
-- elegant implementation here than might be hoped for...
prettyInvPred :: InvariantPred Timed -> String
prettyInvPred = prettyExp . untime . (\(PredTimed e _) -> e)
  where
    untimeTyped :: TypedExp t -> TypedExp Untimed
    untimeTyped (TExp t e) = TExp t (untime e)

    untimeRef:: Ref k t -> Ref k Untimed
    untimeRef (SVar p _ c a) = SVar p Neither c a
    untimeRef (CVar p c a) = CVar p c a
    untimeRef (RArrIdx p e ts xs) = RArrIdx p (untimeRef e) ts (fmap (first untimeTyped) xs)
    untimeRef (RMapIdx p e ts xs) = RMapIdx p (untimeRef e) ts (fmap untimeTyped xs)
    untimeRef (RField p e c x) = RField p (untimeRef e) c x

    untime :: Exp a t -> Exp a Untimed
    untime e = case e of
      And p a b   -> And p (untime a) (untime b)
      Or p a b    -> Or p (untime a) (untime b)
      Impl p a b  -> Impl p (untime a) (untime b)
      Eq p t a b  -> Eq p t (untime a) (untime b)
      LT p a b    -> LT p (untime a) (untime b)
      LEQ p a b   -> LEQ p (untime a) (untime b)
      GT p a b    -> GT p (untime a) (untime b)
      GEQ p a b   -> GEQ p (untime a) (untime b)
      NEq p t a b -> NEq p t (untime a) (untime b)
      Neg p a     -> Neg p (untime a)
      Add p a b   -> Add p (untime a) (untime b)
      Sub p a b   -> Sub p (untime a) (untime b)
      Mul p a b   -> Mul p (untime a) (untime b)
      Div p a b   -> Div p (untime a) (untime b)
      Mod p a b   -> Mod p (untime a) (untime b)
      Exp p a b   -> Exp p (untime a) (untime b)
      Cat p a b   -> Cat p (untime a) (untime b)
      ByStr p a   -> ByStr p a
      ByLit p a   -> ByLit p a
      LitInt p a  -> LitInt p a
      IntMin p a  -> IntMin p a
      IntMax p a  -> IntMax p a
      UIntMin p a -> UIntMin p a
      UIntMax p a -> UIntMax p a
      InRange p a b -> InRange p a (untime b)
      LitBool p a -> LitBool p a
      Array p l -> Array p (fmap untime l)
      Create p f xs v -> Create p f (fmap untimeTyped xs) (fmap untime v)
      IntEnv p a  -> IntEnv p a
      ByEnv p a   -> ByEnv p a
      ITE p x y z -> ITE p (untime x) (untime y) (untime z)
      Slice p a b c -> Slice p (untime a) (untime b) (untime c)
      VarRef p vt k a -> VarRef p vt k (untimeRef a)
      Address c a -> Address c (untime a)
      Mapping p kt vt kvs -> Mapping p kt vt (map (bimap untime untime) kvs)
      MappingUpd p r kt vt kvs -> MappingUpd p (untimeRef r) kt vt (map (bimap untime untime) kvs)

-- | Doc type for terminal output
type DocAnsi = Doc Term.AnsiStyle

-- | prints a Doc, with wider output than the built in `putDoc`
render :: DocAnsi -> IO ()
render doc =
  let opts = LayoutOptions { layoutPageWidth = AvailablePerLine 120 0.9 } in
  Term.renderIO stdout (layoutPretty opts doc)

underline :: DocAnsi -> DocAnsi
underline = annotate Term.underlined

red :: DocAnsi -> DocAnsi
red = annotate (Term.color Term.Red)

yellow :: DocAnsi -> DocAnsi
yellow = annotate (Term.color Term.Yellow)

green :: DocAnsi -> DocAnsi
green = annotate (Term.color Term.Green)

bold :: DocAnsi -> DocAnsi
bold = annotate Term.bold

(<$$>) :: Doc ann -> Doc ann -> Doc ann
(<$$>) x y = vsep [x,y]

string :: String -> DocAnsi
string = pretty

text :: Text.Text -> DocAnsi
text = pretty

class PrettyAnsi a where
  prettyAnsi :: a -> DocAnsi
