import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-! All ten resource-error rows from `script_tests.json` at
`9be056a8a72b624dae9623b2f7bded92c2a21c91`.
Source SHA-256: `bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5`.
Indices are zero-based positions in the complete upstream JSON array. -/

private def limitSourceIndices : List Nat := [827, 828, 829, 830, 831, 832, 833, 912, 914, 915]

private def limitFixtureJson : String := r#"
[
  [
    "NOP",
    "'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'",
    "P2SH,STRICTENC",
    "PUSH_SIZE",
    ">520 byte push"
  ],
  [
    "0",
    "IF 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' ENDIF 1",
    "P2SH,STRICTENC",
    "PUSH_SIZE",
    ">520 byte push in non-executed IF branch"
  ],
  [
    "1",
    "0x61616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161",
    "P2SH,STRICTENC",
    "OP_COUNT",
    ">201 opcodes executed. 0x61 is NOP"
  ],
  [
    "0",
    "IF 0x6161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161 ENDIF 1",
    "P2SH,STRICTENC",
    "OP_COUNT",
    ">201 opcodes including non-executed IF branch. 0x61 is NOP"
  ],
  [
    "1 2 3 4 5 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f",
    "1 2 3 4 5 6 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f",
    "P2SH,STRICTENC",
    "STACK_SIZE",
    ">1,000 stack size (0x6f is 3DUP)"
  ],
  [
    "1 2 3 4 5 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f",
    "1 TOALTSTACK 2 TOALTSTACK 3 4 5 6 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f",
    "P2SH,STRICTENC",
    "STACK_SIZE",
    ">1,000 stack+altstack size"
  ],
  [
    "NOP",
    "0 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f 2DUP 0x616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161",
    "P2SH,STRICTENC",
    "SCRIPT_SIZE",
    "10,001-byte scriptPubKey"
  ],
  [
    "",
    "0 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG 0 0 CHECKMULTISIG",
    "P2SH,STRICTENC",
    "OP_COUNT",
    "202 CHECKMULTISIGS, fails due to 201 op limit"
  ],
  [
    "",
    "NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIG",
    "P2SH,STRICTENC",
    "OP_COUNT",
    "Fails due to 201 script operation limit"
  ],
  [
    "1",
    "NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP NOP 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY 0 0 'a' 'b' 'c' 'd' 'e' 'f' 'g' 'h' 'i' 'j' 'k' 'l' 'm' 'n' 'o' 'p' 'q' 'r' 's' 't' 20 CHECKMULTISIGVERIFY",
    "P2SH,STRICTENC",
    "OP_COUNT",
    ""
  ]
]
"#

example : limitSourceIndices.length = 10 ∧ limitSourceIndices.eraseDups.length = 10 := by
  native_decide

example : ((auditCoreScriptTests rejectingFixtureOracle limitFixtureJson).toOption.map
    fun audit => audit.testRows == 10 && audit.comparedRows == 10 &&
      audit.matchedRows == 10 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

private def nops (count : Nat) : String := String.join (List.replicate count "NOP ")
private def pushes (count : Nat) : String := String.join (List.replicate count "1 ")
private def pushBytes (count : Nat) : String :=
  "0x4d" ++ (if count == 520 then "0802" else "0902") ++
    " 0x" ++ String.join (List.replicate count "00") ++ " "

private def localLimitRows : List (List String) :=
  [["", nops 201 ++ "1", "", "OK"],
   ["", nops 202 ++ "1", "", "OP_COUNT"],
   [nops 201, nops 201 ++ "1", "", "OK", "fresh operation count at each script boundary"],
   ["", "0 IF " ++ nops 199 ++ "ENDIF 1", "", "OK"],
   ["", "0 IF " ++ nops 200 ++ "ENDIF 1", "", "OP_COUNT"],
   ["", "RETURN " ++ nops 202, "", "OP_RETURN"],
   ["", nops 200 ++ "RETURN NOP", "", "OP_RETURN"],
   ["", nops 201 ++ "RETURN", "", "OP_COUNT"],
   ["", nops 200 ++ "CAT", "", "DISABLED_OPCODE"],
   ["", nops 201 ++ "CAT", "", "OP_COUNT"],
   ["", nops 201 ++ "0x50", "", "BAD_OPCODE", "RESERVED does not consume operation count"],
   ["", nops 201 ++ "0x4d", "", "BAD_OPCODE", "truncated push precedes opcode count"],
   ["", nops 201 ++ pushBytes 521, "", "PUSH_SIZE"],
   ["", nops 201 ++ "IF", "", "OP_COUNT", "count precedes control stack underflow"],
   ["", nops 201 ++ "ENDIF", "", "OP_COUNT"],
   ["", pushBytes 520 ++ "DROP 1", "", "OK"],
   ["", pushBytes 521 ++ "DROP 1", "", "PUSH_SIZE"],
   ["", "0 IF " ++ pushBytes 521 ++ "ENDIF 1", "", "PUSH_SIZE"],
   ["", "RETURN " ++ pushBytes 521, "", "OP_RETURN"],
   ["", pushes 1000, "", "OK"],
   ["", pushes 1001, "", "STACK_SIZE"],
   [pushes 1000, "1", "", "STACK_SIZE"],
   ["", pushes 1000 ++ "TOALTSTACK 1", "", "STACK_SIZE"],
   [pushes 999 ++ "TOALTSTACK", "1 1", "", "OK", "alternate stack resets at next script"],
   ["1 TOALTSTACK", "FROMALTSTACK", "", "INVALID_ALTSTACK_OPERATION"],
   ["", nops 200 ++ "1 CHECKMULTISIG", "", "OP_COUNT", "dynamic count before missing key frame"],
   ["", nops 199 ++ "1 CHECKMULTISIG", "", "INVALID_STACK_OPERATION"],
   ["", nops 200 ++ "21 CHECKMULTISIG", "", "PUBKEY_COUNT"],
   ["", nops 201 ++ "21 CHECKMULTISIG", "", "OP_COUNT"],
   ["", nops 200 ++ "-1 CHECKMULTISIG", "", "PUBKEY_COUNT"],
   ["", nops 200 ++ "2147483648 CHECKMULTISIG", "", "SCRIPTNUM"],
   ["", nops 200 ++ "CHECKMULTISIG", "", "INVALID_STACK_OPERATION"],
   ["", nops 201 ++ "CHECKMULTISIG", "", "OP_COUNT"],
   ["", "0 IF 20 CHECKMULTISIG ENDIF " ++ nops 198 ++ "1", "", "OK",
     "inactive multisig counts its opcode but adds no key count"],
   ["", "0 0 0 CHECKMULTISIG", "", "OK", "zero signatures avoid crypto callback"],
   ["", "1 0 0 0 CHECKMULTISIGVERIFY", "", "OK"],
   ["", "1 0 0 CHECKMULTISIG", "NULLDUMMY", "SIG_NULLDUMMY"],
   ["", "0 0 CHECKMULTISIG", "", "INVALID_STACK_OPERATION"],
   ["", "0 IF CHECKSIG ENDIF 1", "", "OK"],
   ["", "RETURN CHECKSIG", "", "OP_RETURN"],
   ["", String.join (List.replicate 19 (pushBytes 520)) ++ pushes 63, "", "OK",
     "exactly 10000 serialized bytes"],
   ["", String.join (List.replicate 19 (pushBytes 520)) ++ pushes 64, "", "SCRIPT_SIZE"],
   ["", "RETURN " ++ pushes 10000, "", "SCRIPT_SIZE", "size precedes first RETURN"],
   [pushes 10001, "RETURN", "", "SCRIPT_SIZE"],
   ["RETURN", pushes 10001, "", "OP_RETURN", "earlier script fails before pubkey size check"]]

example : localLimitRows.length = 45 := by native_decide

example : ((auditCoreScriptTests rejectingFixtureOracle
    (Lean.toJson localLimitRows).compress).toOption.map fun audit =>
      audit.testRows == 45 && audit.matchedRows == 45 &&
      audit.unsupportedRows == 0 && audit.allComparedRowsMatch) = some true := by
  native_decide

private def fixture (script : String) (expected : String) : CoreScriptTest :=
  { witness := none, scriptSigSource := "", scriptPubKeySource := script,
    flagSource := "", expectedError := expected, comments := [] }

-- A reached verifier remains unsupported even for an empty signature.
example : (["0 0 CHECKSIG", "0 0 1 0 1 CHECKMULTISIG"] : List String).all
    (fun script => match prepareCoreFixture (fixture script "OK") with
      | .error .signatureOpcode => true
      | _ => false) = true := by native_decide

-- Resource errors before the verifier are admitted without using its result.
example : ([false, true] : List Bool).all (fun result =>
    (checkCoreFixture (CryptoOracle.pureLeanHashes (fun _ _ _ => result))
      (fixture (nops 201 ++ "0 0 CHECKSIG") "OP_COUNT")).toOption == some true) = true := by
  native_decide

-- An adversarial hash callback would enter CHECKSIG. Fixture execution fixes
-- hashes to the same pure implementation used to establish admission.
private def adversarialOracle : CryptoOracle :=
  { rejectingFixtureOracle with
    sha256 := fun _ => ByteArray.empty
    checkSig := fun _ _ _ => false }

private def hashBranchFixture : CoreScriptTest :=
  fixture "0 SHA256 SIZE IF DROP 1 ELSE DROP 0 0 CHECKSIG ENDIF" "OK"

example : (checkCoreFixture adversarialOracle hashBranchFixture).toOption = some true := by
  native_decide

end LeanMiniscript.Extraction
