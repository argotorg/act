-- Data types for the Act AST after parsing. It is also equipped with position information
-- for printing informative error messages.
{-# LANGUAGE OverloadedStrings #-}

module Act.Syntax.Untyped (module Act.Syntax.Untyped, module Act.Syntax.Types) where

import Data.Aeson
import Data.List (intercalate)
import Data.Text as T (pack)

import EVM.ABI
import Act.Syntax.Types

newtype Act = Main [Contract]
  deriving (Eq, Show)

data IsPayable = Payable | NonPayable
  deriving (Eq, Show)

data Contract = Contract Constructor [Transition]
  deriving (Eq, Show)

data Constructor = Constructor Pn Id Interface IsPayable Iff (Cases Creates) Ensures Invariants
  deriving (Eq, Show)

data Transition = Transition Pn Id Id Interface IsPayable Iff (Cases (StorageUpdates, Maybe Expr)) Ensures
  deriving (Eq, Show)

type Iff = [Expr]

type Ensures = [Expr]

type Invariants = [Expr]

data Interface = Interface Id [Arg]
  deriving (Eq, Ord)

instance Show Interface where
  show (Interface a d) = a <> "(" <> intercalate ", " (fmap show d) <> ")"

type Cases a = [Case a]
  
data Case a = Case Pn Expr a
  deriving (Eq, Show)

type Creates = [Assign]
  
data StorageUpdate = Update Ref Expr
  deriving (Eq, Show)

type StorageUpdates = [StorageUpdate]

data StorageVar = StorageVar Pn ValueType Id
  deriving (Eq, Show)

type Assign = (StorageVar, Expr)

data Arg = Arg ArgType Id
  deriving (Eq, Ord)

instance Show Arg where
  show (Arg t a) = show t <> " " <> a

data TimeTag = Pre | Post | Neither
  deriving (Eq, Show)

data Ref
  = RVar Pn TimeTag Id
  | RVarPre Pn Id
  | RVarPost Pn Id
  | RIndex Pn Ref Expr
  | RField Pn Ref Id
  deriving (Eq, Show)

data Expr
  = EAnd Pn Expr Expr
  | EOr Pn Expr Expr
  | ENot Pn Expr
  | EImpl Pn Expr Expr
  | EEq Pn Expr Expr
  | ENeq Pn Expr Expr
  | ELEQ Pn Expr Expr
  | ELT Pn Expr Expr
  | EGEQ Pn Expr Expr
  | EGT Pn Expr Expr
  | EAdd Pn Expr Expr
  | ESub Pn Expr Expr
  | EITE Pn Expr Expr Expr
  | EMul Pn Expr Expr
  | EDiv Pn Expr Expr
  | EMod Pn Expr Expr
  | EExp Pn Expr Expr
  | ERef Ref
  | ECreate Pn Id [Expr] (Maybe Expr)
  | EArray Pn [Expr]
  | ListConst Expr
  | ECat Pn Expr Expr
  | ESlice Pn Expr Expr Expr
  | ENewaddr Pn Expr Expr
  | ENewaddr2 Pn Expr Expr Expr
  | BYHash Pn Expr
  | BYAbiE Pn Expr
  | StringLit Pn String
  | WildExp Pn
  | EnvExp Pn EthEnv
  | IntLit Pn Integer
  | BoolLit Pn Bool
  | EInRange Pn AbiType Expr
  | AddrOf Pn Expr
  | Mapping Pn [(Expr, Expr)]
  | MappingUpd Pn Ref [(Expr, Expr)]
  deriving (Eq, Show)

data EthEnv
  = Caller
  | Callvalue
  | Origin
  | This
--   | Calldepth
--   | Blockhash
--   | Blocknumber
--   | Difficulty
--   | Chainid
--   | Gaslimit
--   | Coinbase
--   | Timestamp
--   | Nonce
  deriving (Show, Eq)

-- | Types of Ethereum environment variables
ethEnv :: EthEnv -> TValueType AInteger
ethEnv Callvalue = TInteger 256 Unsigned
ethEnv Caller    = TAddress
ethEnv This      = TAddress
ethEnv Origin    = TAddress

instance ToJSON (TValueType a) where
  toJSON (TInteger n Signed)      = object [ "type" .= String "Int"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (TInteger n Unsigned)    = object [ "type" .= String "UInt"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON TUnboundedInt            = object [ "type" .= String "UnboundedInt" ]
  toJSON TAddress                 = object [ "type" .= String "Address" ]
  toJSON TBoolean                 = object [ "type" .= String "Bool" ]
  toJSON TByteStr                 = object [ "type" .= String "Bytes" ]
  toJSON (TStruct fs)             = object [ "type" .= String "Tuple"
                                           , "elemTypes" .= toJSON fs ]

  toJSON (TContract cid)          = object [ "type" .= String "Contract"
                                           , "name" .= cid ]
  toJSON (TArray n t)             = object [ "type" .= String "Array"
                                           , "arrayType" .= toJSON t
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (TMapping k v)           = object [ "type" .= String "Mapping"
                                           , "keyType" .= toJSON k
                                           , "valueType" .= toJSON v ]
                                           
instance ToJSON ValueType where
  toJSON (ValueType vt)           = toJSON vt

instance ToJSON ArgType where
  toJSON (AbiArg abiType) = object [ "kind" .= String "AbiArgument"
                                   , "abitype" .= toJSON abiType
                                   ]
  toJSON (ContractArg _ c) = object [ "kind" .= String "ContractArgument"
                                    , "name" .= c ]

instance ToJSON AbiType where
  toJSON (AbiUIntType n)          = object [ "type" .= String "UInt"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (AbiIntType n)           = object [ "type" .= String "Int"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON AbiAddressType           = object [ "type" .= String "Address" ]
  toJSON AbiBoolType              = object [ "type" .= String "Bool" ]
  toJSON (AbiBytesType n)         = object [ "type" .= String "Bytes"
                                           , "size" .= String (T.pack $ show n) ]
  toJSON AbiBytesDynamicType      = object [ "type" .= String "BytesDynamic" ]
  toJSON AbiStringType            = object [ "type" .= String "String" ]
  toJSON (AbiArrayDynamicType t)  = object [ "type" .= String "ArrayDynamic"
                                        , "arrayType" .= toJSON t ]
  toJSON (AbiArrayType n t)       = object [ "type" .= String "Array"
                                           , "arrayType" .= toJSON t
                                           , "size" .= String (T.pack $ show n) ]
  toJSON (AbiTupleType ts)        = object [ "type" .= String "Tuple"
                                           , "elemTypes" .= toJSON ts ]
  toJSON (AbiFunctionType)        = object [ "type" .= String "Function" ]


-- Create the string that is used to construct the function selector
makeIface :: Interface -> String
makeIface (Interface a decls) =
 a <> "(" <> intercalate "," (fmap (\(Arg argtype _) -> show $ argToAbiType argtype) decls) <> ")"
