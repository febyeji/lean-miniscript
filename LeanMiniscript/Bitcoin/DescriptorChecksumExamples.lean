import LeanMiniscript.Bitcoin.DescriptorChecksum

namespace LeanMiniscript.Bitcoin.DescriptorChecksum

private def succeedsWith (result : Except String String) (expected : String) : Bool :=
  match result with
  | .ok text => text == expected
  | .error _ => false

private def fails {α : Type} (result : Except String α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

/-! Checksum vectors from BIP380 and its Python reference:
https://github.com/bitcoin/bips/blob/master/bip-0380.mediawiki
BIP380 source SHA256: 34e6510bb2eba9445a68eacf3d24d5a4e5f24481477488d5552f674ac81dd5fe
Additional expected values cross-checked with the unmodified C++ checksum
functions from Bitcoin Core revision 9be056a8a72b624dae9623b2f7bded92c2a21c91:
https://github.com/bitcoin/bitcoin/blob/9be056a8a72b624dae9623b2f7bded92c2a21c91/src/script/descriptor.cpp
Core source SHA256: 9fe652a4a8f91068ead31125eb8f41b733299a77fce71741cc2c6ad88c7123ac
They cover all character groups and all three group-padding cases. These
algorithm inputs intentionally include strings outside descriptor grammar. -/

private def referenceVectors : Array (String × String) := #[
  ("", "7h0w2xvg"),
  ("raw(deadbeef)", "89f8spxm"),
  ("raw(deedbeef)", "xj8ljs75"),
  ("raw(deadbeef) ", "4aasm820"),
  (" raw(deadbeef)", "h3kvumkd"),
  ("0123456789()[]", "m9298y58"),
  (",'/*abcdefgh@:$%{}", "t8qnnha8"),
  ("IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~", "rl39lz70"),
  ("ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ", "k0flmwum"),
  ("0", "xvgvxlhq"),
  ("01", "3283levx"),
  ("012", "whc65vvv"),
  ("0123", "c3klgzuk"),
  ("01234", "776xzd2a"),
  ("012345", "vsgmd4v6"),
  ("0123456789()[],'/*abcdefgh@:$%", "v0qq4vfj"),
  ("0123456789()[],'/*abcdefgh@:$%{", "vqj80m3r"),
  ("0123456789()[],'/*abcdefgh@:$%{}", "rx3su4fy"),
  ("0123456789()[],'/*abcdefgh@:$%{}I", "nkwqp9an"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJ", "gdrnac4y"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|", "lvukrd6n"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~", "8n6en4wl"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~i", "dk845c2t"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ij", "6p9terws"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#", "fqgv8ma5"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"", "kcmwlpct"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\", "nnygsvn2"),
  ("0123456789()[],'/*abcdefgh@:$%{}IJKLMNOPQRSTUVWXYZ&+-.;<=>?!^_|~ijklmnopqrstuvwxyzABCDEFGH`#\"\\ ", "fzuaxexw"),
  ("000", "7dst3wr5"),
  ("00I", "q6l9mg0a"),
  ("00i", "t2wh9zmx"),
  ("0I0", "4ape0yh0"),
  ("0II", "ar96sk6e"),
  ("0Ii", "r5256sks"),
  ("0i0", "gymxy6zt"),
  ("0iI", "kn5gwuwz"),
  ("0ii", "c3nqnhcw"),
  ("I00", "xxuwe358"),
  ("I0I", "dkdu8mqu"),
  ("I0i", "npzjdav4"),
  ("II0", "mlx3j0pr"),
  ("III", "9gflcfd2"),
  ("IIi", "wccdxre3"),
  ("Ii0", "s0hrv94c"),
  ("IiI", "juka44uf"),
  ("Iii", "vtenlnsq"),
  ("i00", "8mgppeym"),
  ("i0I", "ev80tlgj"),
  ("i0i", "3jrv5d9y"),
  ("iI0", "09vz7tfd"),
  ("iII", "y4asqpak"),
  ("iIi", "6zj7283l"),
  ("ii0", "5q4khv8n"),
  ("iiI", "2h6ca2t6"),
  ("iii", "p8t2rqlp")]

example : referenceVectors.all (fun (body, expected) =>
    succeedsWith (checksum body) expected) = true := by native_decide

-- BIP380 checksum and charset test vectors, including optional-checksum mode.
example : succeedsWith (validate "raw(deadbeef)#89f8spxm" true) "raw(deadbeef)" = true := by native_decide
example : succeedsWith (addChecksum "raw(deadbeef)") "raw(deadbeef)#89f8spxm" = true := by native_decide
example : succeedsWith (validate "raw(deadbeef)") "raw(deadbeef)" = true := by native_decide
example : fails (validate "raw(deadbeef)" true) = true := by native_decide
example : #["raw(deadbeef)#", "raw(deadbeef)#89f8spxmx", "raw(deadbeef)#89f8spx",
    "raw(deedbeef)#89f8spxm", "raw(deedbeef)##9f8spxm", "raw(Ü)#00000000"].all
    (fun text => fails (validate text) && fails (validate text true)) = true := by native_decide

-- Exact input bytes remain significant, including valid spaces and case.
example : #[" raw(deadbeef)#89f8spxm", "raw(deadbeef) #89f8spxm",
    "RAW(deadbeef)#89f8spxm", "raw(deadbeef)#89F8SPXM", "raw(deadbeef)#89f8spx!",
    "raw(deadbeef)#89f8spxm#", "raw(deadbeef)#89f8spxm#89f8spxm", "#", "##"].all
    (fun text => fails (validate text)) = true := by native_decide
example : #["raw(Ü)", "raw(é)", "raw(deadbeef)\n", "raw(deadbeef)\t", "raw(😀)",
    String.ofList ['r', 'a', 'w', '(', Char.ofNat 0, ')']].all
    (fun text => fails (checksum text) && fails (validate text)) = true := by native_decide
example : fails (addChecksum "raw(deadbeef)#89f8spxm") = true := by native_decide
example : referenceVectors.all (fun (body, expected) =>
    if body.contains '#' then true
    else succeedsWith (validate (body ++ "#" ++ expected) true) body &&
      succeedsWith (addChecksum body) (body ++ "#" ++ expected)) = true := by native_decide

end LeanMiniscript.Bitcoin.DescriptorChecksum
