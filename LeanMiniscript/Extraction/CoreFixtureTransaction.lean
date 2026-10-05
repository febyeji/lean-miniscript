import LeanMiniscript.Bitcoin.LegacySighash

namespace LeanMiniscript.Extraction

open LeanMiniscript.Bitcoin

/-- Bitcoin Core's BuildCreditingTransaction: a null prevout, two OP_0 pushes,
and the fixture output at index zero. Amounts are supplied in satoshis. -/
def coreCreditingTransaction (scriptPubKey : ByteArray) (amount : UInt64) : Transaction where
  version := 1
  locktime := 0
  inputs := #[{
    previousOutput := { txid := ⟨(List.replicate 32 0).toArray⟩, index := 0xffffffff }
    scriptSig := ⟨#[0, 0]⟩
    sequence := 0xffffffff }]
  outputs := #[{ amount := amount, scriptPubKey := scriptPubKey }]

/-- Bitcoin Core's BuildSpendingTransaction for the one-output credit above.
The funding txid is its double-SHA256 digest in wire byte order. Witness is
provided separately and does not enter this non-witness transaction record. -/
def coreSpendingTransaction (scriptSig : ByteArray) (credit : Transaction) : Transaction where
  version := 1
  locktime := 0
  inputs := #[{
    previousOutput := { txid := doubleSHA256 (serializeTransaction credit), index := 0 }
    scriptSig := scriptSig
    sequence := 0xffffffff }]
  outputs := #[{ amount := (credit.outputs[0]!).amount, scriptPubKey := ByteArray.empty }]

/-- Complete transaction inputs shared by legacy, witness-v0 and Taproot fixture execution. -/
structure CoreFixtureTransaction where
  credit : Transaction
  spend : Transaction
  inputIndex : Nat := 0
  amount : UInt64
  spentOutputs : Array TxOutput
  deriving Repr

def coreFixtureTransaction (scriptSig scriptPubKey : ByteArray) (amount : UInt64) :
    CoreFixtureTransaction :=
  let credit := coreCreditingTransaction scriptPubKey amount
  { credit := credit, spend := coreSpendingTransaction scriptSig credit,
    amount := amount, spentOutputs := credit.outputs }

end LeanMiniscript.Extraction
