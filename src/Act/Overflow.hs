{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language ApplicativeDo #-}

module Act.Overflow (checkIntegerBoundsAct) where

import Prelude hiding (GT, LT)

import Act.Syntax.Timing
import Act.Syntax.TypedImplicit
import Act.Type


uint256 :: TValueType AInteger
uint256 = TInteger 256 Unsigned

int2565 :: TValueType AInteger
int2565 = TInteger 256 Signed

-- | Integers should be restricted to int256 or uint256
makeIntegerBoundConstraint :: Pn -> String -> Env -> Exp AInteger Untimed -> Constraint Untimed
makeIntegerBoundConstraint p str env e = BoolCnstr p "" str env (Or nowhere (InRange nowhere uint256 e) (InRange nowhere int2565 e))

-- | Signed operations should have both operands either signed or unsigned
-- In the future, we should use this check to infer the signedness of signed operations
makeSignedOpConstraint :: Pn -> String -> Env -> Exp AInteger Untimed -> Exp AInteger Untimed -> Constraint Untimed
makeSignedOpConstraint p str env e1 e2 = BoolCnstr p "" str env (Or nowhere (And nowhere (InRange nowhere int2565 e1) (InRange nowhere int2565 e2))
                                                                         (And nowhere (InRange nowhere uint256 e1) (InRange nowhere uint256 e2)))


checkIntegerBoundsAct :: Act -> FilePath -> [Constraint Timed]
checkIntegerBoundsAct (Act _store contracts) src = constraintSource src <$> annotate <$> concatMap checkIntegerBoundsContract contracts

-- Note that we only need to popullate the calldata and preconditions field of the env
checkIntegerBoundsContract :: Contract -> [Constraint Untimed]
checkIntegerBoundsContract (Contract ctor behvs) =
    checkIntegerBoundsConstructor ctor ++ concatMap checkIntegerBoundsBehaviour behvs

checkIntegerBoundsConstructor :: Constructor -> [Constraint Untimed]
checkIntegerBoundsConstructor (Constructor _ (Interface _ decls) _ pre cases _ invs) =
    -- add calldata to env
    let env = addCalldata decls emptyEnv in
    -- add preconditions to env
    let env' = addPreconds pre env in 
    -- check expressions in preconditions and cases
    concatMap (checkIntegerBoundsExp env') pre ++
    concatMap (checkIntegerBoundsConstrCase env') cases
    -- we ignore invariants and postconditions for now


checkIntegerBoundsBehaviour :: Behaviour -> [Constraint Untimed]
checkIntegerBoundsBehaviour (Behaviour _ _ (Interface _ decls) _ pre cases _) =
    -- add calldata to env
    let env = addCalldata decls emptyEnv in
    -- add preconditions to env
    let env' = addPreconds pre env in 
    -- check expressions in preconditions and cases
    concatMap (checkIntegerBoundsExp env') pre ++
    concatMap (checkIntegerBoundsBehvCase env') cases
    -- we ignore postconditions for now

checkIntegerBoundsConstrCase :: Env -> Ccase Untimed -> [Constraint Untimed]
checkIntegerBoundsConstrCase env (Case _ c upds) =
    checkIntegerBoundsExp env c ++ 
    addIffs [c] (concatMap (\(Update _ _ e) -> checkIntegerBoundsExp env e) upds)

checkIntegerBoundsBehvCase :: Env -> Bcase Untimed -> [Constraint Untimed]
checkIntegerBoundsBehvCase env (Case _ c (upds, ret)) =
    checkIntegerBoundsExp env c ++ 
    addIffs [c] (concatMap (\(Update _ _ e) -> checkIntegerBoundsExp env e) upds ++
    (case ret of
        Just (TExp _ e)  -> checkIntegerBoundsExp env e
        Nothing -> []))


    
checkIntegerBoundsExp :: forall a. Env -> Exp a Untimed -> [Constraint Untimed]
checkIntegerBoundsExp env (And _ e1 e2) = checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (Or _ e1 e2)  = checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (Impl _ e1 e2) = 
    -- Not sure if it makes sense to add [e1] in the preconditions of e2 here, but otherwise we have a problem
    checkIntegerBoundsExp env e1 ++ (addIffs [e1] $ checkIntegerBoundsExp env e2)
checkIntegerBoundsExp env (Neg _ e)     = checkIntegerBoundsExp env e
checkIntegerBoundsExp env (LT p e1 e2)  = 
    let cnstr = makeSignedOpConstraint p "Operands of < must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (LEQ p e1 e2) = 
    let cnstr = makeSignedOpConstraint p "Operands of <= must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (GEQ p e1 e2) = 
    let cnstr = makeSignedOpConstraint p "Operands of >= must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (GT p e1 e2)  = 
    let cnstr = makeSignedOpConstraint p "Operands of > must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Add p e1 e2) = 
    let cnstr = makeIntegerBoundConstraint p "Result of + must be in the range of int256 or uint256" env e in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Sub p e1 e2) = 
    let cnstr = makeIntegerBoundConstraint p "Result of - must be in the range of int256 or uint256" env e in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Mul p e1 e2) = 
    let cnstr = makeIntegerBoundConstraint p "Result of * must be in the range of int256 or uint256" env e in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Div p e1 e2) = 
    let cnstr = makeSignedOpConstraint p "Operands of / must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Mod p e1 e2) = 
    let cnstr = makeSignedOpConstraint p "Operands of % must be both signed or both unsigned" env e1 e2 in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env e@(Exp p e1 e2) = 
    let cnstr = makeIntegerBoundConstraint p "Result of ^ must be in the range of int256 or uint256" env e in
    cnstr : checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (ITE _ cond e1 e2) =
    checkIntegerBoundsExp env cond ++ checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (Eq _ _ e1 e2) =
    checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (NEq _ _ e1 e2) =
    checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp _ (VarRef _ _ _) = []
checkIntegerBoundsExp _ (IntEnv _ _) = []
checkIntegerBoundsExp _ (LitInt _ _) = []
checkIntegerBoundsExp _ (LitBool _ _) = []
checkIntegerBoundsExp _ (ByStr _ _) = []
checkIntegerBoundsExp _ (ByLit _ _) = []
checkIntegerBoundsExp _ (ByEnv _ _) = []
checkIntegerBoundsExp env (Address _ _ e) = checkIntegerBoundsExp env e
checkIntegerBoundsExp _ (IntMin _ _) = []
checkIntegerBoundsExp _ (IntMax _ _) = []
checkIntegerBoundsExp _ (UIntMin _ _) = []
checkIntegerBoundsExp _ (UIntMax _ _) = []
checkIntegerBoundsExp env (InRange _ _ e) = checkIntegerBoundsExp env e
checkIntegerBoundsExp env (Cat _ e1 e2) = checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2
checkIntegerBoundsExp env (Slice _ e1 e2 e3) = checkIntegerBoundsExp env e1 ++ checkIntegerBoundsExp env e2 ++ checkIntegerBoundsExp env e3
checkIntegerBoundsExp env (Array _ es) = concatMap (checkIntegerBoundsExp env) es
checkIntegerBoundsExp env (Create _ _ args _) = concatMap (\ (TExp _ e) -> checkIntegerBoundsExp env e) args
checkIntegerBoundsExp env (Mapping _ _ _ kvs) = concatMap (\(k,v) -> checkIntegerBoundsExp env k ++ checkIntegerBoundsExp env v) kvs
checkIntegerBoundsExp env (MappingUpd _ _ _ _ kvs) = concatMap (\(k,v) -> checkIntegerBoundsExp env k ++ checkIntegerBoundsExp env v) kvs
