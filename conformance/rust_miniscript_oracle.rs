use miniscript::bitcoin::{key::XOnlyPublicKey, PublicKey};
use miniscript::expression::{FromTree, Tree};
use miniscript::{Miniscript, Segwitv0, Tap};

const KEY_A: &str = "02d7924d4f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e";
const KEY_B: &str = "03b506a1dbe57b4bf48c95e0c7d417b87dd3b4349d290d2e7e9ba72c912652d80a";
const HASH_256: &str = "4ae81572f06e1b88fd5ced7a1a000945432e83e1551e6f721ee9c00b8cc33260";
const HASH_160: &str = "4ae81572f06e1b88fd5ced7a1a00094543a00069";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn dump_wsh(name: &str, expression: &str) {
    let tree = Tree::from_str(expression).unwrap();
    let miniscript = Miniscript::<PublicKey, Segwitv0>::from_tree(tree.root()).unwrap();
    println!(
        "{name}|{expression}|{}",
        hex(miniscript.encode().as_bytes())
    );
}

fn dump_tap(name: &str, expression: &str) {
    let tree = Tree::from_str(expression).unwrap();
    let miniscript = Miniscript::<XOnlyPublicKey, Tap>::from_tree(tree.root()).unwrap();
    println!(
        "{name}|{expression}|{}",
        hex(miniscript.encode().as_bytes())
    );
}

fn main() {
    let wsh = [
        ("zero", "0".to_owned()),
        ("one", "1".to_owned()),
        ("pk_k", format!("pk_k({KEY_A})")),
        ("pk_h", format!("pk_h({KEY_A})")),
        ("older", "older(42)".to_owned()),
        ("after", "after(500000000)".to_owned()),
        ("sha256", format!("sha256({HASH_256})")),
        ("hash256", format!("hash256({HASH_256})")),
        ("ripemd160", format!("ripemd160({HASH_160})")),
        ("hash160", format!("hash160({HASH_160})")),
        ("and_v", format!("and_v(v:older(42),pk({KEY_B}))")),
        ("and_b", format!("and_b(pk({KEY_A}),s:pk({KEY_B}))")),
        ("or_b", format!("or_b(pk({KEY_A}),s:pk({KEY_B}))")),
        ("or_c", format!("or_c(pk({KEY_A}),v:older(42))")),
        ("or_d", format!("or_d(pk({KEY_A}),pk({KEY_B}))")),
        ("or_i", format!("or_i(pk({KEY_A}),pk({KEY_B}))")),
        (
            "andor",
            format!("andor(pk({KEY_A}),pk({KEY_B}),pk({KEY_A}))"),
        ),
        ("a", format!("a:pk({KEY_A})")),
        ("s", format!("s:pk({KEY_A})")),
        ("c", format!("c:pk_k({KEY_A})")),
        ("d", "dv:older(42)".to_owned()),
        ("v", "v:older(42)".to_owned()),
        ("j", format!("j:pk({KEY_A})")),
        ("n", format!("n:pk({KEY_A})")),
        ("thresh", format!("thresh(2,pk({KEY_A}),s:pk({KEY_B}))")),
        ("multi", format!("multi(2,{KEY_A},{KEY_B})")),
        ("surface_core", "1".to_owned()),
        ("surface_pk", format!("pk({KEY_A})")),
        ("surface_pkh", format!("pkh({KEY_A})")),
        ("surface_and_n", format!("and_n(pk({KEY_A}),pk({KEY_B}))")),
        ("surface_t", "tv:older(42)".to_owned()),
        ("surface_l", format!("l:pk({KEY_A})")),
        ("surface_u", format!("u:pk({KEY_A})")),
    ];

    for (name, expression) in wsh {
        dump_wsh(name, &expression);
    }

    let tap_key_a = &KEY_A[2..];
    let tap_key_b = &KEY_B[2..];
    dump_tap("multi_a", &format!("multi_a(2,{tap_key_a},{tap_key_b})"));
}
