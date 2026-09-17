import LeanMiniscript.Bitcoin.Serialization
import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Bitcoin

/-- Transaction IDs are bytes in wire order, not reversed display hex. -/
structure OutPoint where
  txid : ByteArray
  index : UInt32
  deriving Repr, Inhabited

structure TxInput where
  previousOutput : OutPoint
  scriptSig : ByteArray := ByteArray.empty
  sequence : UInt32
  deriving Repr, Inhabited

structure TxOutput where
  amount : UInt64
  scriptPubKey : ByteArray
  deriving Repr, Inhabited

/-- Fields committed by signature hashing, with bounded integer widths.
    Witness is supplied separately because it is not committed wholesale. -/
structure Transaction where
  version : UInt32
  inputs : Array TxInput
  outputs : Array TxOutput
  locktime : UInt32
  deriving Repr, Inhabited

def serializeOutPoint (outpoint : OutPoint) : ByteArray :=
  outpoint.txid ++ ⟨(unsignedLE 4 outpoint.index.toNat).toArray⟩

def serializeTxInput (input : TxInput) : ByteArray :=
  serializeOutPoint input.previousOutput ++ serializeByteVector input.scriptSig ++
    ⟨(unsignedLE 4 input.sequence.toNat).toArray⟩

def serializeTxOutput (output : TxOutput) : ByteArray :=
  ⟨(unsignedLE 8 output.amount.toNat).toArray⟩ ++ serializeByteVector output.scriptPubKey

/-- Non-witness transaction serialization. Txid lengths are checked by the
    signature-hash boundary; this serializer is a raw field serializer. -/
def serializeTransaction (tx : Transaction) : ByteArray :=
  ⟨(unsignedLE 4 tx.version.toNat ++ compactSize tx.inputs.size).toArray⟩ ++
    tx.inputs.foldl (fun bytes input => bytes ++ serializeTxInput input) ByteArray.empty ++
    ⟨(compactSize tx.outputs.size).toArray⟩ ++
    tx.outputs.foldl (fun bytes output => bytes ++ serializeTxOutput output) ByteArray.empty ++
    ⟨(unsignedLE 4 tx.locktime.toNat).toArray⟩

def Transaction.signedVersion (tx : Transaction) : Int :=
  if tx.version.toNat < 2147483648 then tx.version.toNat
  else (tx.version.toNat : Int) - 4294967296

end LeanMiniscript.Bitcoin
