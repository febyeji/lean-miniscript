import LeanMiniscript.Extraction.BitcoinCoreAudit

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-! Pinned NOP, RETURN and legacy opcode-error fixtures from
`src/test/data/script_tests.json` at `bitcoinCoreScriptTestsCommit`.
Source SHA-256: `bc23cb1dfa760d50042f534da23cbbe4b6fbb03d7def0b64f8de049453d6ead5`.
The inventory includes every row containing the new NOP names, RETURN, disabled
or reserved names, standalone reserved/invalid bytes, or one of their error tags.
Unsupported timelock, signature, P2SH and SIG_PUSHONLY cases retain source indices. -/

private def nopErrorFixtureJson : String := r#"
[
  ["0", "IF 0x50 ENDIF 1", "P2SH,STRICTENC", "OK", "0x50 is reserved (ok if not executed)"],
  ["0", "IF VER ELSE 1 ENDIF", "P2SH,STRICTENC", "OK", "VER non-functional (ok if not executed)"],
  ["0", "IF RESERVED RESERVED1 RESERVED2 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK", "RESERVED ok in un-executed IF"],
  ["0", "IF 1 IF RETURN ELSE RETURN ELSE RETURN ENDIF ELSE 1 IF 1 ELSE RETURN ELSE 1 ENDIF ELSE RETURN ENDIF ADD 2 EQUAL", "P2SH,STRICTENC", "OK", "Nested ELSE ELSE"],
  ["1", "NOTIF 0 NOTIF RETURN ELSE RETURN ELSE RETURN ENDIF ELSE 0 NOTIF 1 ELSE RETURN ELSE 1 ENDIF ELSE RETURN ENDIF ADD 2 EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "IF RETURN ENDIF 1", "P2SH,STRICTENC", "OK", "RETURN only works if executed"],
  ["1", "NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4 NOP5 NOP6 NOP7 NOP8 NOP9 NOP10 1 EQUAL", "P2SH,STRICTENC", "OK"],
  ["'NOP_1_to_10' NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4 NOP5 NOP6 NOP7 NOP8 NOP9 NOP10", "'NOP_1_to_10' EQUAL", "P2SH,STRICTENC", "OK"],
  ["0", "IF NOP10 ENDIF 1", "P2SH,STRICTENC,DISCOURAGE_UPGRADABLE_NOPS", "OK", "Discouraged NOPs are allowed if not executed"],
  ["0", "IF 0xba ELSE 1 ENDIF", "P2SH,STRICTENC", "OK", "opcodes above MAX_OPCODE invalid if executed"],
  ["0", "IF 0xbb ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xbc ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xbd ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xbe ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xbf ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc0 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc1 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc2 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc3 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc4 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc5 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc6 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc7 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc8 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xc9 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xca ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xcb ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xcc ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xcd ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xce ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xcf ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd0 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd1 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd2 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd3 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd4 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd5 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd6 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd7 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd8 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xd9 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xda ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xdb ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xdc ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xdd ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xde ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xdf ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe0 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe1 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe2 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe3 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe4 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe5 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe6 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe7 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe8 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xe9 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xea ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xeb ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xec ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xed ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xee ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xef ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf0 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf1 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf2 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf3 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf4 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf5 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf6 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf7 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf8 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xf9 ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xfa ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xfb ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xfc ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xfd ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xfe ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["0", "IF 0xff ELSE 1 ENDIF", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP1 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP4 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP5 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP6 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP7 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP8 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP9 1", "P2SH,STRICTENC", "OK"],
  ["NOP", "NOP10 1", "P2SH,STRICTENC", "OK"],
  ["0x4c01", "0x01 NOP", "P2SH,STRICTENC", "BAD_OPCODE", "PUSHDATA1 with not enough bytes"],
  ["0x4d0200ff", "0x01 NOP", "P2SH,STRICTENC", "BAD_OPCODE", "PUSHDATA2 with not enough bytes"],
  ["0x4e03000000ffff", "0x01 NOP", "P2SH,STRICTENC", "BAD_OPCODE", "PUSHDATA4 with not enough bytes"],
  ["1", "IF 0x50 ENDIF 1", "P2SH,STRICTENC", "BAD_OPCODE", "0x50 is reserved"],
  ["1", "IF VER ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "VER non-functional"],
  ["0", "IF VERIF ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "VERIF illegal everywhere"],
  ["0", "IF ELSE 1 ELSE VERIF ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "VERIF illegal everywhere"],
  ["0", "IF VERNOTIF ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "VERNOTIF illegal everywhere"],
  ["0", "IF ELSE 1 ELSE VERNOTIF ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "VERNOTIF illegal everywhere"],
  ["1", "IF RETURN ELSE ELSE 1 ENDIF", "P2SH,STRICTENC", "OP_RETURN", "Multiple ELSEs"],
  ["1", "IF 1 ELSE ELSE RETURN ENDIF", "P2SH,STRICTENC", "OP_RETURN"],
  ["1", "RETURN", "P2SH,STRICTENC", "OP_RETURN"],
  ["1", "DUP IF RETURN ENDIF", "P2SH,STRICTENC", "OP_RETURN"],
  ["1", "RETURN 'data'", "P2SH,STRICTENC", "OP_RETURN", "canonical prunable txout format"],
  ["0 IF", "RETURN ENDIF 1", "P2SH,STRICTENC", "UNBALANCED_CONDITIONAL", "still prunable because IF/ENDIF can't span scriptSig/scriptPubKey"],
  ["'a' 'b'", "CAT", "P2SH,STRICTENC", "DISABLED_OPCODE", "CAT disabled"],
  ["'a' 'b' 0", "IF CAT ELSE 1 ENDIF", "P2SH,STRICTENC", "DISABLED_OPCODE", "CAT disabled"],
  ["'abc' 1 1", "SUBSTR", "P2SH,STRICTENC", "DISABLED_OPCODE", "SUBSTR disabled"],
  ["'abc' 1 1 0", "IF SUBSTR ELSE 1 ENDIF", "P2SH,STRICTENC", "DISABLED_OPCODE", "SUBSTR disabled"],
  ["'abc' 2 0", "IF LEFT ELSE 1 ENDIF", "P2SH,STRICTENC", "DISABLED_OPCODE", "LEFT disabled"],
  ["'abc' 2 0", "IF RIGHT ELSE 1 ENDIF", "P2SH,STRICTENC", "DISABLED_OPCODE", "RIGHT disabled"],
  ["'abc'", "IF INVERT ELSE 1 ENDIF", "P2SH,STRICTENC", "DISABLED_OPCODE", "INVERT disabled"],
  ["1 2 0 IF AND ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "AND disabled"],
  ["1 2 0 IF OR ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "OR disabled"],
  ["1 2 0 IF XOR ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "XOR disabled"],
  ["2 0 IF 2MUL ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "2MUL disabled"],
  ["2 0 IF 2DIV ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "2DIV disabled"],
  ["2 2 0 IF MUL ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "MUL disabled"],
  ["2 2 0 IF DIV ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "DIV disabled"],
  ["2 2 0 IF MOD ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "MOD disabled"],
  ["2 2 0 IF LSHIFT ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "LSHIFT disabled"],
  ["2 2 0 IF RSHIFT ELSE 1 ENDIF", "NOP", "P2SH,STRICTENC", "DISABLED_OPCODE", "RSHIFT disabled"],
  ["2 DUP MUL", "4 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["2 DUP DIV", "1 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["2 2MUL", "4 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["2 2DIV", "1 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["7 3 MOD", "1 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["2 2 LSHIFT", "8 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["2 1 RSHIFT", "1 EQUAL", "P2SH,STRICTENC", "DISABLED_OPCODE", "disabled"],
  ["1", "NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4 NOP5 NOP6 NOP7 NOP8 NOP9 NOP10 2 EQUAL", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["'NOP_1_to_10' NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4 NOP5 NOP6 NOP7 NOP8 NOP9 NOP10", "'NOP_1_to_11' EQUAL", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "NOP1", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP4", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP5", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP6", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP7", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP8", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP9", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["1", "NOP10", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["NOP10", "1", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS", "Discouraged NOP10 in scriptSig"],
  ["1 0x01 0xb9", "HASH160 0x14 0x15727299b05b45fdaf9ac9ecf7565cfe27c3e567 EQUAL", "P2SH,DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS", "Discouraged NOP10 in redeemScript"],
  ["0x50", "1", "P2SH,STRICTENC", "BAD_OPCODE", "opcode 0x50 is reserved"],
  ["1", "IF 0xba ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE", "opcodes above MAX_OPCODE invalid if executed"],
  ["1", "IF 0xbb ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xbc ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xbd ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xbe ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xbf ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc0 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc1 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc2 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc3 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc4 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc5 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc6 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc7 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc8 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xc9 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xca ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xcb ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xcc ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xcd ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xce ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xcf ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd0 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd1 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd2 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd3 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd4 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd5 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd6 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd7 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd8 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xd9 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xda ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xdb ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xdc ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xdd ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xde ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xdf ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe0 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe1 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe2 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe3 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe4 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe5 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe6 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe7 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe8 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xe9 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xea ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xeb ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xec ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xed ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xee ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xef ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf0 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf1 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf2 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf3 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf4 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf5 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf6 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf7 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf8 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xf9 ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xfa ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xfb ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xfc ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xfd ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xfe ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1", "IF 0xff ELSE 1 ENDIF", "P2SH,STRICTENC", "BAD_OPCODE"],
  ["1 IF 1 ELSE", "0xff ENDIF", "P2SH,STRICTENC", "UNBALANCED_CONDITIONAL", "invalid because scriptSig and scriptPubKey are processed separately"],
  ["NOP1", "NOP10", "P2SH,STRICTENC", "EVAL_FALSE"],
  ["1", "VER", "P2SH,STRICTENC", "BAD_OPCODE", "OP_VER is reserved"],
  ["1", "VERIF", "P2SH,STRICTENC", "BAD_OPCODE", "OP_VERIF is reserved"],
  ["1", "VERNOTIF", "P2SH,STRICTENC", "BAD_OPCODE", "OP_VERNOTIF is reserved"],
  ["1", "RESERVED", "P2SH,STRICTENC", "BAD_OPCODE", "OP_RESERVED is reserved"],
  ["1", "RESERVED1", "P2SH,STRICTENC", "BAD_OPCODE", "OP_RESERVED1 is reserved"],
  ["1", "RESERVED2", "P2SH,STRICTENC", "BAD_OPCODE", "OP_RESERVED2 is reserved"],
  ["1", "0xba", "P2SH,STRICTENC", "BAD_OPCODE", "0xba == MAX_OPCODE + 1"],
  ["NOP1 0x01 1", "HASH160 0x14 0xda1745e9b549bd0bfa1a569971c77eba30cd5a4b EQUAL", "P2SH,STRICTENC", "SIG_PUSHONLY"],
  ["0 0x01 0x50", "HASH160 0x14 0xece424a6bb6ddf4db592c0faed60685047a361b1 EQUAL", "P2SH,STRICTENC", "BAD_OPCODE", "OP_RESERVED in P2SH should fail"],
  ["0 0x01 VER", "HASH160 0x14 0x0f4d7845db968f2a81b530b6f3c1d6246d4c7e01 EQUAL", "P2SH,STRICTENC", "BAD_OPCODE", "OP_VER in P2SH should fail"],
  ["0x47 0x3044022018a2a81a93add5cb5f5da76305718e4ea66045ec4888b28d84cb22fae7f4645b02201e6daa5ed5d2e4b2b2027cf7ffd43d8d9844dd49f74ef86899ec8e669dfd39aa01 NOP8 0x23 0x2103363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640ac", "HASH160 0x14 0x215640c2f72f0d16b4eced26762035a42ffed39a EQUAL", "", "OK", "P2SH(P2PK) with non-push scriptSig but no P2SH or SIGPUSHONLY"],
  ["0x47 0x304402203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c022054e1c258c2981cdfba5df1f46661fb6541c44f77ca0092f3600331abfffb125101 NOP8", "0x21 0x03363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640 CHECKSIG", "P2SH", "OK", "P2PK with non-push scriptSig but with P2SH validation"],
  ["0x47 0x3044022018a2a81a93add5cb5f5da76305718e4ea66045ec4888b28d84cb22fae7f4645b02201e6daa5ed5d2e4b2b2027cf7ffd43d8d9844dd49f74ef86899ec8e669dfd39aa01 NOP8 0x23 0x2103363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640ac", "HASH160 0x14 0x215640c2f72f0d16b4eced26762035a42ffed39a EQUAL", "P2SH", "SIG_PUSHONLY", "P2SH(P2PK) with non-push scriptSig but no SIGPUSHONLY"],
  ["0x47 0x3044022018a2a81a93add5cb5f5da76305718e4ea66045ec4888b28d84cb22fae7f4645b02201e6daa5ed5d2e4b2b2027cf7ffd43d8d9844dd49f74ef86899ec8e669dfd39aa01 NOP8 0x23 0x2103363d90d447b00c9c99ceac05b6262ee053441c7e55552ffe526bad8f83ff4640ac", "HASH160 0x14 0x215640c2f72f0d16b4eced26762035a42ffed39a EQUAL", "SIGPUSHONLY", "SIG_PUSHONLY", "P2SH(P2PK) with non-push scriptSig but not P2SH"]
]
"#

private def nopErrorSourceIndices : List Nat :=
  [28, 31, 32, 56, 57, 58, 223, 224, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 397, 400, 401, 402, 403, 404, 405, 406, 616, 617, 618, 619, 622, 623, 624, 625, 626, 644, 645, 654, 655, 656, 657, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 730, 731, 732, 733, 734, 735, 736, 737, 738, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 834, 835, 836, 837, 838, 839, 840, 841, 919, 920, 921, 1105, 1106, 1107, 1108]

private def excludedSourceRows : List (Nat × String) :=
  [(223, "inactive-timelock.CHECKLOCKTIMEVERIFY"), (224, "inactive-timelock.CHECKLOCKTIMEVERIFY"), (737, "inactive-timelock.CHECKLOCKTIMEVERIFY"), (738, "inactive-timelock.CHECKLOCKTIMEVERIFY"), (749, "p2sh"), (919, "expected-error.SIG_PUSHONLY"), (920, "p2sh"), (921, "p2sh"), (1106, "signature-result"), (1107, "expected-error.SIG_PUSHONLY"), (1108, "expected-error.SIG_PUSHONLY")]

example : nopErrorSourceIndices.length = 225 ∧
    nopErrorSourceIndices.eraseDups.length = 225 := by
  native_decide

-- Every admitted row matches its upstream tag; explicit exclusions remain observable.
example : ((auditCoreScriptTests rejectingFixtureOracle nopErrorFixtureJson).toOption.map
    fun audit => audit.testRows == 225 && audit.comparedRows == 214 &&
      audit.matchedRows == 214 && audit.unsupportedRows == 11 &&
      audit.allComparedRowsMatch &&
      audit.unsupported.map (fun row =>
        (nopErrorSourceIndices[row.index]?.getD 0, row.reason.detailCategory)) ==
        excludedSourceRows) = some true := by
  native_decide

private def nopSourceFixtures : List (String × String × Opcode) :=
  [("NOP1", "0xb0", .OP_NOP1), ("NOP4", "0xb3", .OP_NOP4),
   ("NOP5", "0xb4", .OP_NOP5), ("NOP6", "0xb5", .OP_NOP6),
   ("NOP7", "0xb6", .OP_NOP7), ("NOP8", "0xb7", .OP_NOP8),
   ("NOP9", "0xb8", .OP_NOP9), ("NOP10", "0xb9", .OP_NOP10),
   ("RETURN", "0x6a", .OP_RETURN)]

example : nopSourceFixtures.all (fun (name, raw, opcode) =>
    [name, raw].all fun source =>
      match parseCoreScriptSource source with
      | .ok [.op actual] => actual == opcode
      | _ => false) = true := by
  native_decide

private def localOpcodeErrorJson : String := r#"
[
  ["", "0 VERIFY RETURN 0xff", "", "VERIFY"],
  ["", "RETURN 0x02 0x01", "", "OP_RETURN"],
  ["", "0 VERIFY 0x4c", "", "VERIFY"],
  ["", "RETURN CAT", "", "OP_RETURN"],
  ["", "CAT RETURN", "", "DISABLED_OPCODE"],
  ["", "NOP1 CAT", "DISCOURAGE_UPGRADABLE_NOPS", "DISCOURAGE_UPGRADABLE_NOPS"],
  ["", "CAT NOP1", "DISCOURAGE_UPGRADABLE_NOPS", "DISABLED_OPCODE"],
  ["", "NOP1 CAT", "", "DISABLED_OPCODE"],
  ["", "0 IF CAT ENDIF 1", "", "DISABLED_OPCODE"],
  ["", "0 IF 0xff ENDIF 1", "", "OK"],
  ["", "0 IF VERIF ENDIF 1", "", "BAD_OPCODE"],
  ["", "0 IF VERNOTIF ENDIF 1", "", "BAD_OPCODE"],
  ["", "0 IF 0x4c", "", "BAD_OPCODE"],
  ["", "0 IF RETURN 0xff ENDIF 1", "", "OK"],
  ["", "0 IF CAT", "", "DISABLED_OPCODE"],
  ["", "0 IF 0xff", "", "UNBALANCED_CONDITIONAL"],
  ["", "0xff CAT", "", "BAD_OPCODE"],
  ["", "0x4c01", "", "BAD_OPCODE"],
  ["", "0x4d00", "", "BAD_OPCODE"],
  ["", "0x4e000000", "", "BAD_OPCODE"],
  ["RETURN", "0x4c", "", "OP_RETURN"],
  ["0 VERIFY", "CAT", "", "VERIFY"],
  ["1 TOALTSTACK", "0 IF 0xff ENDIF FROMALTSTACK", "", "INVALID_ALTSTACK_OPERATION"],
  ["1", "0 IF 0xff ENDIF", "", "OK"],
  ["", "0x03 0x7e65ff DROP 0 IF 0xff ENDIF 1", "MINIMALDATA", "OK"],
  ["", "0 IF 0x01 0xff DROP ENDIF 1", "MINIMALDATA", "OK"],
  ["", "0 IF 0xba 0xff ENDIF 1", "", "OK"],
  ["", "1 IF 0xba 0xff ENDIF", "", "BAD_OPCODE"]
]
"#

-- Earlier executed failures precede later malformed pushes and disabled opcodes.
-- Raw fallback retains inactive-branch state and resets the alternate stack between scripts.
example : ((auditCoreScriptTests rejectingFixtureOracle localOpcodeErrorJson).toOption.map
    fun audit => audit.testRows == 28 && audit.comparedRows == 28 &&
      audit.matchedRows == 28 && audit.unsupportedRows == 0 &&
      audit.allComparedRowsMatch) = some true := by
  native_decide

private def fixture (scriptSig scriptPubKey expected : String) (flags : String := "") :
    CoreScriptTest :=
  { witness := none, scriptSigSource := scriptSig, scriptPubKeySource := scriptPubKey,
    flagSource := flags, expectedError := expected, comments := [] }

private def disabledFixtures : List (String × String) :=
  [("CAT", "0x7e"), ("SUBSTR", "0x7f"), ("LEFT", "0x80"), ("RIGHT", "0x81"),
   ("INVERT", "0x83"), ("AND", "0x84"), ("OR", "0x85"), ("XOR", "0x86"),
   ("2MUL", "0x8d"), ("2DIV", "0x8e"), ("MUL", "0x95"), ("DIV", "0x96"),
   ("MOD", "0x97"), ("LSHIFT", "0x98"), ("RSHIFT", "0x99")]

-- Every disabled byte fails in both active and inactive branches, in either spelling.
example : disabledFixtures.all (fun (name, raw) => [name, raw].all fun source =>
    ([source, "0 IF " ++ source ++ " ENDIF 1"] : List String).all fun script =>
      (checkCoreFixture rejectingFixtureOracle (fixture "" script "DISABLED_OPCODE")).toOption ==
        some true) = true := by
  native_decide

-- Disabled/reserved legacy bytes stay outside the shared Script AST.
example : (disabledFixtures ++ [("RESERVED", "0x50"), ("VER", "0x62"),
    ("VERIF", "0x65"), ("VERNOTIF", "0x66"), ("RESERVED1", "0x89"),
    ("RESERVED2", "0x8a")]).all (fun (name, raw) => [name, raw].all fun source =>
      (parseCoreScriptSource source).toOption.isNone) = true := by
  native_decide

-- Source-order execution distinguishes a nonminimal push from an earlier RETURN.
example : ([("0x4c0101 DROP 0 IF 0xff ENDIF 1", "MINIMALDATA"),
    ("RETURN 0x4c0101 0xff", "OP_RETURN")] : List (String × String)).all
    (fun (script, error) =>
      (checkCoreFixture rejectingFixtureOracle
        (fixture "" script error "MINIMALDATA")).toOption == some true) = true := by
  native_decide

-- Resource failures are compared at execution, preserving their precedence.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" (String.join (List.replicate 202 "NOP ") ++ "0xff") "OP_COUNT")).toOption =
      some true := by native_decide

example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" (String.join (List.replicate 10001 "0 ") ++ "0xff") "SCRIPT_SIZE")).toOption =
      some true := by native_decide

-- Witness semantics remain excluded; unreachable signature calls are admitted.
example : (match checkCoreFixture rejectingFixtureOracle
    { (fixture "" "RETURN 0xff" "OP_RETURN") with witness := some (.arr #[]) } with
    | .error .witnessCase => true
    | _ => false) = true := by
  native_decide

example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" "RETURN CHECKSIG 0xff" "OP_RETURN")).toOption = some true := by
  native_decide

-- Valid unmodeled SHA1 and CODESEPARATOR bytes retain their unsupported byte and offset.
example : ([("0xa7", 0xa7), ("0xab", 0xab)] : List (String × UInt8)).all
    (fun (source, byte) => match checkCoreFixture rejectingFixtureOracle
        (fixture "" source "BAD_OPCODE") with
      | .error (.legacyScriptPubKey (.opcode offset actual)) => offset == 0 && actual == byte
      | _ => false) = true := by
  native_decide

-- A raw fallback executes PUSH_SIZE before an inactive opcode marker.
private def oversizedPushSource : String :=
  "0 IF 0x4d0902 0x" ++ String.join (List.replicate 521 "00") ++ " ENDIF 0xff"

example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" oversizedPushSource "PUSH_SIZE")).toOption = some true := by
  native_decide

-- A 520-byte push is accepted; bad opcode bytes inside its payload remain data.
private def maximumPushSource : String :=
  "0x4d0802 0x" ++ String.join (List.replicate 520 "ff") ++
    " DROP 0 IF 0xff ENDIF 1"

example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" maximumPushSource "OK" "MINIMALDATA")).toOption = some true := by
  native_decide

-- The post-instruction stack check precedes a later raw opcode failure.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture "" (String.join (List.replicate 1001 "0 ") ++ "0xff") "STACK_SIZE")).toOption =
      some true := by
  native_decide

-- Inactive raw instructions retain the main stack at its allowed maximum.
example : (checkCoreFixture rejectingFixtureOracle
    (fixture (String.join (List.replicate 999 "1 "))
      "0 IF 0xff ENDIF 1" "OK")).toOption = some true := by
  native_decide

-- P2SH recognition requires the exact 23-byte encoding; PUSHDATA1 is ordinary Script.
private def p2shHashBytes : String := String.join (List.replicate 20 "00")

example : (match checkCoreFixture rejectingFixtureOracle
    (fixture "RETURN 0xff" ("HASH160 0x14 0x" ++ p2shHashBytes ++ " EQUAL")
      "OP_RETURN" "P2SH") with
    | .error .p2shEvaluation => true
    | _ => false) = true := by
  native_decide

example : (checkCoreFixture rejectingFixtureOracle
    (fixture "RETURN 0xff" ("HASH160 0x4c14 0x" ++ p2shHashBytes ++ " EQUAL")
      "OP_RETURN" "P2SH")).toOption = some true := by
  native_decide

end LeanMiniscript.Extraction
