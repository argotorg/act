 {-# LANGUAGE GADTs #-}
 {-# LANGUAGE DataKinds #-}
 {-# LANGUAGE TypeFamilies #-}
 {-# LANGUAGE FlexibleInstances #-}
 {-# LANGUAGE ScopedTypeVariables #-}
 {-# LANGUAGE MultiParamTypeClasses #-}
 {-# LANGUAGE RecordWildCards #-}
 {-# LANGUAGE OverloadedStrings #-}
 {-# LANGUAGE OverloadedRecordDot #-}

module Act.HEVM_utils where

import Prelude hiding (GT, LT)

import Data.Containers.ListUtils (nubOrd)
import Data.List
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Control.Monad.ST (stToIO, ST)
import Control.Monad.Reader
import Control.Monad 

import Act.Syntax.Typed

import qualified EVM.Types as EVM
import EVM.Types (VM(..), SMTCex(..))
import EVM.Expr hiding (op2, inRange)
import EVM.SymExec hiding (isPartial, abstractVM, loadSymVM)
import EVM.Solvers
import qualified EVM.Format as Format
import qualified EVM.Fetch as Fetch
import qualified EVM
import EVM.FeeSchedule (feeSchedule)
import EVM.Effects
import EVM.ABI
import EVM.Format

-- TODO move this to HEVM
type Calldata = (EVM.Expr EVM.Buf, [EVM.Prop])
-- Create a calldata that matches the interface of a certain behaviour
-- or constructor. Use an abstract txdata buffer as the base.


showMsg :: App m => String -> m ()
showMsg s = liftIO $ putStrLn s

defaultActConfig :: Config
defaultActConfig = Config
  { dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , dumpTrace = False
  , numCexFuzz = 0
  , onlyCexFuzz = False
  , decomposeStorage = False
  , promiseNoReent = False
  , maxBufSize = 64
  , maxWidth = 100
  , maxDepth = Nothing
  , verb = 0
  , simp = True
  }


debugActConfig :: Config
debugActConfig = defaultActConfig { dumpQueries = True, dumpExprs = True, dumpEndStates = True, debug = True }

makeCalldata :: Id -> Interface -> Calldata
makeCalldata name iface@(Interface _ decls) =
  let
    mkArg :: Arg -> CalldataFragment
    mkArg (Arg argtype x) = symAbiArg (T.pack x) $ argToAbiType argtype
    makeSig = T.pack $ makeIface name iface
    calldatas = fmap mkArg decls
    (cdBuf, props) = combineFragments calldatas (EVM.ConcreteBuf "")
    withSelector = writeSelector cdBuf makeSig
    sizeConstraints
      = (bufLength withSelector EVM..>= cdLen calldatas)
        EVM..&& (bufLength withSelector EVM..< (EVM.Lit (2 ^ (64 :: Integer))))
  in (withSelector, sizeConstraints:props)

makeCtrCalldata :: Interface -> Calldata
makeCtrCalldata (Interface _ decls) =
  let
    mkArg :: Arg -> CalldataFragment
    mkArg (Arg argtype x) = symAbiArg (T.pack x) $ argToAbiType argtype
    calldatas = fmap mkArg decls
    -- We need to use a concrete buf as a base here because hevm bails when trying to execute with an abstract buf
    -- This is because hevm ends up trying to execute a codecopy with a symbolic size, which is unsupported atm
    -- This is probably unsound, but theres not a lot we can do about it at the moment...
    (cdBuf, props) = combineFragments' calldatas 0 (EVM.ConcreteBuf "")
  in (cdBuf, props)

-- TODO move to HEVM
combineFragments' :: [CalldataFragment] -> EVM.W256 -> EVM.Expr EVM.Buf -> (EVM.Expr EVM.Buf, [EVM.Prop])
combineFragments' fragments start base = go (EVM.Lit start) fragments (base, [])
  where
    go :: EVM.Expr EVM.EWord -> [CalldataFragment] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> (EVM.Expr EVM.Buf, [EVM.Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        St p w -> go (add idx (EVM.Lit 32)) rest (writeWord idx w buf, p <> ps)
        s -> error $ "unsupported cd fragment: " <> show s

checkPartial :: App m => [EVM.Expr EVM.End] -> m ()
checkPartial nodes =
  when (any isPartial nodes) $
  do showMsg ""
     showMsg "WARNING: hevm was only able to partially explore the given contract due to the following issues:"
     showMsg ""
     showMsg . T.unpack . T.unlines . fmap (Format.indent 2 . ("- " <>)) . fmap Format.formatPartial . nubOrd $ (getPartials nodes)


iterConfig :: IterConfig
iterConfig = IterConfig
  { maxIter = Nothing
  , askSmtIters = 1
  , loopHeuristic = StackBased
  }

-- | decompiles the given EVM bytecode into a list of Expr branches
getRuntimeBranches :: App m => SolverGroup -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> Calldata -> [EVM.Prop] -> Int -> m [EVM.Expr EVM.End]
getRuntimeBranches solvers contracts calldata precond fresh = do
  prestate <- liftIO $ stToIO $ abstractVM contracts calldata precond fresh
  expr <- interpret (Fetch.oracle solvers Nothing) iterConfig prestate runExpr
  let simpl = simplify expr
  let nodes = flattenExpr simpl
  checkPartial nodes
  pure nodes


-- | decompiles the given EVM initcode into a list of Expr branches
getInitcodeBranches :: App m => SolverGroup -> BS.ByteString -> IsPayable -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> Calldata -> [EVM.Prop] -> Int -> m [EVM.Expr EVM.End]
getInitcodeBranches solvers initcode payable contracts calldata precond fresh = do
  initVM <- liftIO $ stToIO $ abstractInitVM initcode payable contracts calldata precond fresh
  expr <- interpret (Fetch.oracle solvers Nothing) iterConfig initVM runExpr
  let simpl = simplify expr
  let nodes = flattenExpr simpl
  checkPartial nodes
  pure nodes

abstractInitVM :: BS.ByteString -> IsPayable -> [(EVM.Expr EVM.EAddr, EVM.Contract)] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> [EVM.Prop] -> Int -> ST s (EVM.VM EVM.Symbolic s)
abstractInitVM contractCode payable contracts cd precond fresh = do
  let value = EVM.TxValue
  let code = EVM.InitCode contractCode (fst cd)
  vm <- loadSymVM (EVM.SymAddr "entrypoint", initialContract payable code) contracts value cd True fresh
  pure $ vm { constraints = vm.constraints <> precond }

initialContract :: IsPayable -> EVM.ContractCode -> EVM.Contract
initialContract isPayable code = EVM.Contract
  { EVM.code        = code
  , EVM.storage     = EVM.ConcreteStore mempty
  , EVM.tStorage    = EVM.ConcreteStore mempty
  , EVM.origStorage = EVM.ConcreteStore mempty
  , EVM.balance     = if isPayable == Payable then EVM.TxValue else EVM.Lit 0
  , EVM.nonce       = if EVM.isCreation code then Just 1 else Just 0
  , EVM.codehash    = EVM.hashcode code
  , EVM.opIxMap     = EVM.mkOpIxMap code
  , EVM.codeOps     = EVM.mkCodeOps code
  , EVM.external    = False
  }
abstractVM :: [(EVM.Expr EVM.EAddr, EVM.Contract)] -> (EVM.Expr EVM.Buf, [EVM.Prop]) -> [EVM.Prop] -> Int -> ST s (EVM.VM EVM.Symbolic s)
abstractVM contracts cd precond fresh = do
  let value = EVM.TxValue
  let (c, cs) = findInitContract
  vm <- loadSymVM c cs value cd False fresh
  pure $ vm { constraints = vm.constraints <> precond }

  where
    findInitContract :: ((EVM.Expr 'EVM.EAddr, EVM.Contract), [(EVM.Expr 'EVM.EAddr, EVM.Contract)])
    findInitContract =
      case partition (\(a, _) -> a == EVM.SymAddr "entrypoint") contracts of
        ([c], cs) -> (c, cs)
        _ -> error $ "Internal error: address entrypoint expected exactly once " <> show contracts


loadSymVM
  :: (EVM.Expr EVM.EAddr, EVM.Contract)
  -> [(EVM.Expr EVM.EAddr, EVM.Contract)]
  -> EVM.Expr EVM.EWord
  -> (EVM.Expr EVM.Buf, [EVM.Prop])
  -> Bool
  -> Int
  -> ST s (EVM.VM EVM.Symbolic s)
loadSymVM (entryaddr, entrycontract) othercontracts callvalue cd create fresh =
  (EVM.makeVm $ EVM.VMOpts
     { contract = entrycontract
     , otherContracts = othercontracts
     , calldata = cd
     , baseState = EVM.AbstractBase
     , value = callvalue
     , priorityFee = 0
     , address = entryaddr
     , caller = EVM.SymAddr "caller"
     , origin = EVM.SymAddr "origin"
     , gas = ()
     , gaslimit = 0xffffffffffffffff
     , number = EVM.Lit 0
     , timestamp = EVM.Lit 0
     , coinbase = EVM.SymAddr "coinbase"
     , prevRandao = 42069
     , maxCodeSize = 0xffffffff
     , blockGaslimit = 0
     , gasprice = 0
     , baseFee = 0
     , schedule = feeSchedule
     , chainId = 1
     , create = create
     , txAccessList = mempty
     , allowFFI = False
     , freshAddresses = fresh
     , beaconRoot = 0
     })


-- We reimplement this function only to be able to include printing of address balances
formatCex :: EVM.Expr EVM.Buf -> Maybe Sig -> SMTCex -> T.Text
formatCex cd sig m@(SMTCex _ addrs _ store blockContext txContext) = T.unlines $
  [ "Calldata:", indent 2 cd' ]
  <> storeCex
  <> txCtx
  <> blockCtx
  <> addrsCex
  where
    -- we attempt to produce a model for calldata by substituting all variables
    -- and buffers provided by the model into the original calldata expression.
    -- If we have a concrete result then we display it, otherwise we display
    -- `Any`. This is a little bit of a hack (and maybe unsound?), but we need
    -- it for branches that do not refer to calldata at all (e.g. the top level
    -- callvalue check inserted by solidity in contracts that don't have any
    -- payable functions).
    cd' = case sig of
      Nothing -> case (defaultSymbolicValues $ subModel m cd) of
        Right k -> prettyBuf $ EVM.Expr.concKeccakSimpExpr k
        Left err -> T.pack err
      Just (Sig n ts) -> prettyCalldata m cd n ts

    storeCex :: [T.Text]
    storeCex
      | M.null store = []
      | otherwise =
          [ "Storage:"
          , indent 2 $ T.unlines $ M.foldrWithKey (\key val acc ->
              ("Addr " <> (T.pack . show $ key)
                <> ": " <> (T.pack $ show (M.toList val))) : acc
            ) mempty store
          ]

    txCtx :: [T.Text]
    txCtx
      | M.null txContext = []
      | otherwise =
        [ "Transaction Context:"
        , indent 2 $ T.unlines $ M.foldrWithKey (\key val acc ->
            (showTxCtx key <> ": " <> (T.pack $ show val)) : acc
          ) mempty (filterSubCtx txContext)
        ]

    addrsCex :: [T.Text]
    addrsCex
      | M.null addrs = []
      | otherwise =
          [ "Addrs:"
          , indent 2 $ T.unlines $ M.foldrWithKey (\key val acc ->
              ((T.pack . show $ key) <> ": " <> (T.pack $ show val)) : acc
            ) mempty addrs
          ]

    -- strips the frame arg from frame context vars to make them easier to read
    showTxCtx :: EVM.Expr EVM.EWord -> T.Text
    showTxCtx (EVM.TxValue) = "TxValue"
    showTxCtx x = T.pack $ show x

    -- strips all frame context that doesn't come from the top frame
    filterSubCtx :: M.Map (EVM.Expr EVM.EWord) EVM.W256 -> M.Map (EVM.Expr EVM.EWord) EVM.W256
    filterSubCtx = M.filterWithKey go
      where
        go :: EVM.Expr EVM.EWord -> EVM.W256 -> Bool
        go (EVM.TxValue) _ = True
        go (EVM.Balance {}) _ = True
        go (EVM.Gas {}) _ = error "TODO: Gas"
        go _ _ = False

    blockCtx :: [T.Text]
    blockCtx
      | M.null blockContext = []
      | otherwise =
        [ "Block Context:"
        , indent 2 $ T.unlines $ M.foldrWithKey (\key val acc ->
            (T.pack $ show key <> ": " <> show val) : acc
          ) mempty txContext
        ]
