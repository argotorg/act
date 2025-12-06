{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE InstanceSigs #-}

{-|
Module      : Syntax.TypedExplicit
Description : AST data types where all implicit timings have been made explicit.
-}
module Act.Syntax.TypedExplicit (module Act.Syntax.TypedExplicit) where

import qualified Act.Syntax.Typed as Typed
import Act.Syntax.Typed (Timing(..),setPre,setPost)

-- Reexports
import Act.Syntax.Typed as Act.Syntax.TypedExplicit hiding (Timing(..),Timable(..),Time,Neither,Act,Contract,Invariant,InvariantPred,Constructor,Behaviour,Cases,StorageUpdate,TypedRef,Exp,TypedExp,Ref)
import Act.Syntax.Typed as Act.Syntax.TypedExplicit (pattern Act, pattern Contract, pattern Invariant, pattern Constructor, pattern Behaviour, pattern Exp)


-- We shadow all timing-agnostic AST types with explicitly timed versions.
type Act              = Typed.Act              Timed
type Contract         = Typed.Contract         Timed
type Invariant        = Typed.Invariant        Timed
type InvariantPred    = Typed.InvariantPred    Timed
type Constructor      = Typed.Constructor      Timed
type Behaviour        = Typed.Behaviour        Timed
type Cases          a = Typed.Cases          a Timed
type StorageUpdate    = Typed.StorageUpdate    Timed
type TypedRef         = Typed.TypedRef         Timed
type Ref            k = Typed.Ref            k Timed
type Exp            a = Typed.Exp            a Timed
type TypedExp         = Typed.TypedExp         Timed

------------------------------------------
-- * How to make all timings explicit * --
------------------------------------------

instance Annotatable Typed.Act where
  annotate (Typed.Act store act) = Typed.Act store $ fmap annotate act

instance Annotatable Typed.Contract where
  annotate (Typed.Contract ctor behv) = Typed.Contract (annotate ctor) (fmap annotate behv)

instance Annotatable Typed.Invariant where
  annotate inv@Invariant{..} = inv
    { _ipreconditions = setPre <$> _ipreconditions
    , _istoragebounds = setPre <$> _istoragebounds
    , _predicate = annotate _predicate
    }

instance Annotatable Typed.InvariantPred where
  annotate (PredUntimed p) = PredTimed (setPre p) (setPost p)

instance Annotatable Typed.Constructor where
  annotate ctor@Constructor{..} = ctor
    { _cpreconditions = setPre <$> _cpreconditions
    , _cpostconditions = setPost <$> _cpostconditions
    , _ccases = annotateCCase <$> _ccases
    , _invariants  = annotate <$> _invariants
    }

instance Annotatable Typed.Behaviour where
  annotate behv@Behaviour{..} = behv
    { _preconditions = setPre <$> _preconditions
    , _cases = annotateCase <$> _cases
    }

instance Annotatable Typed.StorageUpdate where
  -- The timing in items only refers to the timing of mapping indices of a
  -- storage update. Hence, it should be Pre
  annotate :: Typed.StorageUpdate Untimed -> Typed.StorageUpdate Timed
  annotate (Update typ item expr) = Update typ (setPre item) (setPre expr)

annotateCCase :: (Typed.Exp ABoolean Untimed, [Typed.StorageUpdate Untimed]) -> (Typed.Exp ABoolean Timed, [Typed.StorageUpdate Timed])
annotateCCase (cond, upds) = (setPre cond, annotate <$> upds)

annotateCase :: (Typed.Exp ABoolean Untimed, ([Typed.StorageUpdate Untimed], Maybe (Typed.TypedExp Timed))) -> (Typed.Exp ABoolean Timed, ([Typed.StorageUpdate Timed], Maybe (Typed.TypedExp Timed)))
annotateCase (cond, (upds, ret)) = (setPre cond, (annotate <$> upds, ret))
