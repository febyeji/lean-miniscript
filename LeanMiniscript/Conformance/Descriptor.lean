import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Miniscript.DescriptorParser
import LeanMiniscript.Miniscript.OutputDescriptor

namespace LeanMiniscript.Conformance.Descriptor

open LeanMiniscript.Miniscript

open LeanMiniscript.TestSupport (hex)

private def compressed : PubKey := PubKey.ofBytes
  (hex "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")

private def uncompressed : PubKey := PubKey.ofBytes
  (hex "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")

private def matchesScript (descriptor : OutputDescriptor) (script : String) : Bool :=
  match compileOutputDescriptor descriptor with
  | .ok result => result.scriptPubKey == hex script
  | .error _ => false

example : matchesScript (.pk compressed)
    "210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798ac" = true := by
  native_decide

example : matchesScript (.pkh compressed)
    "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac" = true := by
  native_decide

example : matchesScript (.pk uncompressed)
    "410479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8ac" = true := by
  native_decide

example : matchesScript (.wpkh compressed)
    "0014751e76e8199196d454941c45d1b3a323f1433bd6" = true := by
  native_decide

example : matchesScript (.sh (.pk compressed))
    "a91423b0ad3477f2178bc0b3eed26e4e6316f4e83aa187" = true := by
  native_decide

example : matchesScript (.sh (.pkh compressed))
    "a914cd7b44d0b03f2d026d1e586d7ae18903b0d385f687" = true := by
  native_decide

example : matchesScript (.raw (hex "51")) "51" = true := by
  native_decide

example : (match deriveOutputDescriptor s!"sh(pk(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798))" with
    | .ok result => result.scriptPubKey == hex "a91423b0ad3477f2178bc0b3eed26e4e6316f4e83aa187"
    | .error _ => false) = true := by
  native_decide

/-! ## `addr()` and `combo()`

Address vectors are every non-private-key row of Bitcoin Core's
`key_io_valid.json`, and the rejected strings are every row of
`key_io_invalid.json`, pinned at 9be056a8a72b624dae9623b2f7bded92c2a21c91
(the same files at Core df0dc1e2d2059213e49a9f115fd55a9f0119d26c):
key_io_valid.json SHA256: 90bd1d35d12763e0d00c5400b2c9fe551e532a821e1e466c20cad3aced70a7fe
key_io_invalid.json SHA256: c3ca74ddad7c01faaca7c26063537feb73ff2be03eb7fc83a42a655d2979261d
The valid rows cover mainnet, testnet4, signet, and regtest. -/

private def keyIoAddresses : Array (String × String) := #[
  ("1FsSia9rv4NeEwvJ2GvXrX7LyxYspbN2mo",
   "76a914a31c06bd463e3923bc1aadbde48b16976c08071788ac"),
  ("36j4NfKv6Akva9amjWrLG6MuSQym1GuEmm",
   "a914373b819a068f32b7a6b38b6b38729647cfde01c287"),
  ("mzK2FFDEhxqHcmrJw1ysqFkVyhUULo45hZ",
   "76a914ce28b26c57472737f5c3561a1761185bd8589a4388ac"),
  ("2NC2hEhe28ULKAJkW5MjZ3jtTMJdvXmByvK",
   "a914ce0bba75891ff9ec60148d4bd4a09ee2dc5c933187"),
  ("mww4LvqtTMKvmeQvizPz2EQv26xTneWrbg",
   "76a914b4110ba93ac54afc14da3bdd19614774a2d55d2988ac"),
  ("2N1r7aC69VHeE7yQJPDLi9T1PYq4wnwvjuT",
   "a9145e5a35ab44b3efaea5129ba22b88ba3e2976614587"),
  ("n4fajahJrAuKbN7uNsKjLjQkz9Qn5ewJXQ",
   "76a914fdeca3b08e38af53d7c4c60e3ad208ce5066441088ac"),
  ("2MxFajLApXpYk4VodBSZSt7rw8y4ryABkfA",
   "a91436e9f191e0b75036a77f65e2eaa4752443233fbe87"),
  ("bc1qvyq0cc6rahyvsazfdje0twl7ez82ndmuac2lhv",
   "00146100fc6343edc8c874496cb2f5bbfec88ea9b77c"),
  ("bc1qyucykdlhp62tezs0hagqury402qwhk589q80tqs5myh3rxq34nwqhkdhv7",
   "002027304b37f70e94bc8a0fbf500e0c957a80ebda87280ef58214d92f119811acdc"),
  ("bc1p83n3au0rjylefxq2nc2xh2y4jzz4pm6zxj4mw5pagdjjr2a9f36s6jjnnu",
   "51203c671ef1e3913f94980a9e146ba895908550ef4234abb7503d436521aba54c75"),
  ("bc1z2rksukkjr8",
   "520250ed"),
  ("tb1qcrh3yqn4nlleplcez2yndq2ry8h9ncg3qh7n54",
   "0014c0ef1202759fff90ff19128936814321ee59e111"),
  ("tb1quyl9ujpgwr2chdzdnnalen48sup245vdfnh2jxhsuq3yx80rrwlq5hqfe4",
   "0020e13e5e482870d58bb44d9cfbfccea78702aad18d4ceea91af0e022431de31bbe"),
  ("tb1p35n52jy6xkm4wd905tdy8qtagrn73kqdz73xe4zxpvq9t3fp50aqk3s6gz",
   "51208d2745489a35b75734afa2da43817d40e7e8d80d17a26cd4460b0055c521a3fa"),
  ("tb1rgv5m6uvdk3kc7qsuz0c79v88ycr5w4wa",
   "53104329bd718db46d8f021c13f1e2b0e726"),
  ("tb1q3vya2h5435jkugq2few7dmktlrwq4ejmfaw7kr",
   "00148b09d55e958d256e200a4e5de6eecbf8dc0ae65b"),
  ("tb1qxkhrl2s6ttrclckldruea0e8anhrehffl8xv7t0pdyrzm08v2hyqy408nf",
   "002035ae3faa1a5ac78fe2df68f99ebf27ecee3cdd29f9cccf2de169062dbcec55c8"),
  ("tb1pae5um27ahn8n73pgexe3kcwlp8dhswpn684h2k2w6t9a7w3eq65qephd5y",
   "5120ee69cdabddbccf3f4428c9b31b61df09db783833d1eb75594ed2cbdf3a3906a8"),
  ("tb1rx9n9g37az8mu236e5jpxdt0m67y4fuq8rhs0ss3djnm0kscfrwvq0ntlyg",
   "532031665447dd11f7c54759a48266adfbd78954f0071de0f8422d94f6fb43091b98"),
  ("bcrt1qdavt4j2sd7dlhqsavtnfxvzppw6k7qy97tmnu9",
   "00146f58bac9506f9bfb821d62e69330410bb56f0085"),
  ("bcrt1qan8gntac7z7me2ejt4hpru42ad2f759fmy0m3ejvs98656znv7eqga4uhv",
   "0020ecce89afb8f0bdbcab325d6e11f2aaeb549f50a9d91fb8e64c814faa685367b2"),
  ("bcrt1pfwxjqvtt4tcxrtdluukfmy2dv7xd2qzdfy6kajv5nwn4yam3wxkq3553uh",
   "51204b8d20316baaf061adbfe72c9d914d678cd5004d49356ec9949ba752777171ac"),
  ("bcrt1sx6p8njlx7h9mc2agz4yg82dzne23050ncq72cneeecez2pst8mahn8xecsf8g6hzx94420",
   "6028368279cbe6f5cbbc2ba8154883a9a29e5517d1f3c03cac4f39ce3225060b3efb799cd9c412746ae2"),
  ("1FjL87pn8ky6Vbavd1ZHeChRXtoxwRGCRd",
   "76a914a19331b7b2627e663e25a7b001e4c0dcc5e21bc788ac"),
  ("3BZECeAH8gSKkjrTx8PwMrNQBLG18yHpvf",
   "a9146c382dcdf5b284760c8e3fead91f7422cd76aa8787"),
  ("n4YNbYuFdPwFrxSP8sjHFbAhUbLMUiY9jE",
   "76a914fc8f9851f3c1e4719cd0b8e4816dd4e88c72e52888ac"),
  ("2NAeQVZayzVFAtgeC3iYJsjpjWDmsDph71A",
   "a914bedc797342c03fd7a346c4c7857ca03d467013b687"),
  ("mnCBpkNMJEJLehgdEkzSo2eioniyJMxLpZ",
   "76a914493c455551e48a1423263b62b127b436106a685488ac"),
  ("2N5sNHomeNJDZv67AcFx9ES7FBZY4jx9KDA",
   "a9148a776a0f34d56b63e7c595f2b205dbe1c393617a87"),
  ("mfhE6jAUwjUDNZhaX1PAsDTKfneQF2Nshc",
   "76a91401f15a4cc063dae4f4d56b89bfbc8bcc9ae5387c88ac"),
  ("2MxNm1VHyVU4RuP3u1c1v5aQLk2dQjwy1Qk",
   "a91438456f7c076356abadcc67b92ad777eb20fb9f8887"),
  ("bc1qhxt04s5xnpy0kxw4x99n5hpdf5pmtzpqs52es2",
   "0014b996fac2869848fb19d5314b3a5c2d4d03b58820"),
  ("bc1qgc9ljrvdf2e0zg9rmmq86xklqwfys7r6wptjlacdgrcdc7sa6ggqu4rrxf",
   "0020460bf90d8d4ab2f120a3dec07d1adf039248787a70572ff70d40f0dc7a1dd210"),
  ("bc1pve739yap4uxjvfk0jrey69078u0gasm2nwvv483ec6zkzulgw9xqu4w9fd",
   "5120667d1293a1af0d2626cf90f24d15fe3f1e8ec36a9b98ca9e39c6856173e8714c"),
  ("bc1zmjtqxkzs89",
   "5202dc96"),
  ("tb1ql4k5ayv7p7w0t0ge7tpntgpkgw53g2payxkszr",
   "0014fd6d4e919e0f9cf5bd19f2c335a03643a914283d"),
  ("tb1q9jx3x2qqdpempxrcfgyrkjd5fzeacaqj4ua7cs7fe2sfd2wdaueq5wn26y",
   "00202c8d1328006873b098784a083b49b448b3dc7412af3bec43c9caa096a9cdef32"),
  ("tb1pdswckwd9ym5yf5eyzg8j4jjwnzla8y0tf9cp7aasfkek0u29sz9qfr00yf",
   "51206c1d8b39a526e844d324120f2aca4e98bfd391eb49701f77b04db367f145808a"),
  ("tb1r0ecpfxg2udhtc556gqrpwwhk4sw3f0kc",
   "53107e7014990ae36ebc529a4006173af6ac"),
  ("tb1q6mwf89hnqhlu8txjgjfs4s7p93ugffn3k062ll",
   "0014d6dc9396f305ffc3acd244930ac3c12c7884a671"),
  ("tb1qafrjalu4d73dql0czau9j6z422434kef235mzljf48ckd5xz3sys09jm97",
   "0020ea472eff956fa2d07df8177859685552ab1adb295469b17e49a9f166d0c28c09"),
  ("tb1pwst9qszjrhuv2e7as0flcq9gm698v6gdxzz9e87p07s8rssdx3zqklm3vf",
   "512074165040521df8c567dd83d3fc00a8de8a76690d30845c9fc17fa071c20d3444"),
  ("tb1r3ss76jtsuxe8c8c8lxsehnpak55ylrgr345pww076l536ahjr6jsydamx3",
   "53208c21ed4970e1b27c1f07f9a19bcc3db5284f8d038d681739fed7e91d76f21ea5"),
  ("bcrt1q65nhlm4hf2ptg3t264al57p7wjxj2c3s6kyt83",
   "0014d5277feeb74a82b4456ad57bfa783e748d256230"),
  ("bcrt1qawvc90lpytw3z3k9etdx54l0exq5f5sqfzu5e45kjnl6slwayeeqx2dyac",
   "0020eb9982bfe122dd1146c5cada6a57efc98144d20048b94cd69694ffa87ddd2672"),
  ("bcrt1p39a4s4vdcw9kqa8w2t0rp7aj8kfxyw7mce5sk5d70x6wnnmpvt7skf2kxy",
   "5120897b58558dc38b6074ee52de30fbb23d92623bdbc6690b51be79b4e9cf6162fd"),
  ("bcrt1s489d9fhmyel0vzfqsrmew4x7r80asuqesm5hgqacy35daflcyufh3j8cgdtflvt99ph05m",
   "6028a9cad2a6fb267ef6092080f79754de19dfd8701986e97403b82468dea7f8271378c8f843569fb165"),
  ("1G9A9j6W8TLuh6dEeVwWeyibK1Uc5MfVFV",
   "76a914a614da54daacdb8861f451a0b7e3c27cdf8a099e88ac"),
  ("33GA3ZXbw5o5HeUrBEaqkWXFYYZmdxGRRP",
   "a914113ca1afeb49ff3abf176ffa19c2a2b4df19712a87"),
  ("mwgS2HRbjyfYxFnR1nF9VKLvmdgMfFBmGq",
   "76a914b14ce7070b53cb0e4b5b5f6e253e876990aeca2e88ac"),
  ("2MwBVrJQ76BdaGD76CTmou8cZzQYLpe4NqU",
   "a9142b2c149cde619eae3d7fe995243b76a3417541aa87"),
  ("mfnJ8tEkqKNFE5YaHTXFxyHk2mnDK2fvDh",
   "76a91402e6cd77e649ad8b281271f158fc964ca3f66cb088ac"),
  ("2My83D67ir7K8PPzeT6mE2oth3ZwNTVRS9F",
   "a9144074d84d32ff62da7b1b3c61925b934bfeb34b0587")]

private def derivesScript (descriptor script : String) : Bool :=
  match deriveOutputDescriptor descriptor with
  | .ok result => result.scriptPubKey == hex script && result.redeemScript.isNone &&
      result.witnessScript.isNone && result.taprootLeaves.isEmpty
  | .error _ => false

example : keyIoAddresses.size = 54 := by native_decide

example : keyIoAddresses.all (fun (address, script) =>
    derivesScript s!"addr({address})" script) = true := by
  native_decide

private def keyIoInvalid : Array String := #[
  "",
  "x",
  "1GAdfviErV2Ew95FPtZyikz2qGP3gyCB6Hyu94sedAkPpA523m3fQwps9YKUZkKgQckGPKhRsFR",
  "37G2kMDLpmWVhimxRdzwNfE8JFvWXnJYnVcXeeGrek2qumdJuK7XArcVVpRtLLjRra3t64BEPF2",
  "giymtio7u7oqWtmC9YnvAEKkLF3JQpAdkEFkVJKYrVDfaLbhaDpX1ihfF2vZmya1i61fwLPC3YQ",
  "8iVk9nLM3nYwRuwypjy9NK5rsuZH7BbrQRZ1pgcQmvMnjAgRXD",
  "cPTVQ1hbo4qdoysf6Jx5GthqucNmdfqt6J2pZRFeXv8Ep7Kmjqud",
  "cQbR2Ny85XFBzUMx3Ed6HsTLw2pVruSgPvt5AofnBUnhiv86gYeW",
  "2UB3iG3VJbX2TRrMwm6ssWskgvU9VjFBYSqCzwqkrihCwo7mg4mtS4WuGZgxTKuxf5A3EcotYEymz",
  "cQe12pqwPR6ExtZKfrKf1q4b3CTh1Qi7MwuvMvzs79nWXDvESfBJ",
  "tc1qeul5g2xfkvdkrhcfmdursv73ad64jnkjl9c40f",
  "bt1pq65rzej5glw3ra79gav6fqnx4haa0z257qr3mc8cggkefahmgvyseufhc0",
  "tb13hty4qmumlwpp6chxjvcyzza4duqgtmxw3xhm3u9ahj4nyhtwz8eq7ynrj4",
  "bcrt1r2qxpwuge",
  "bc10uexgzna2dpfk0vjt35srz6a27ps6m0l89jweznt83n2sqn2fx4hvn9ym5af8wut34sfrqhk3",
  "tb1qum6uh0pt4q253qaf520929737v63w5gf",
  "bcrt1q888ryfgxpvl0k7vum8zpyar2u2sexvdhkf38ue37yknmqq0ycrwpl3w48y",
  "bc1qdsuzmn04k2z8vryw8l4dj8m5ygqgnne5n",
  "tb1qlj8es50nc8j8r8xshrjgzmw5azx89efghmw8ju6zcqla0g6xcnrstsjz7k",
  "bcrt1qzwmyj0z924g7fzs5yvnrkc43y76RVyr2lh5t4r",
  "bc1qpu6d26mrulzetu4jqhd7rsunv9aqru26f5c4j8",
  "tb1qun6d26ufh77ghny6u5u8cwz9da7qwc6k4wkuceae9tth06eqlw0syupl4w",
  "bcrt1qj7g2jps453kj9htk9cxyyc2nxe69x4kzzmth7v",
  "bc1p702xksx4z3uqf0u2phllxkfe5cgu0adxptqs0uelx0tqt8e885sqryes2l",
  "tb1z7gmh0v6pc30z4xum76lmw8w86yswrlmw",
  "bcrt1sjsrw6nun4h502cr97xmnyyuhkr22q0s6efrgtu",
  "2UVPFpGYnLHJezFzjUo42our6PMEoozzRdM",
  "2MygHQjE1U33q3LSC53p69YqFjP8PihumJAF",
  "KzNbAQ4mexfAxa6RKBzHQqfoTycaeWpv2p",
  "2jDPrDfAKihCGPbPD9ztY8TswAia4V8Bc6vx",
  "4VQUNG1hG64QFtaNyQZQWDdwpxB275Pwb3tvyPt2HDxB8Mi2MgH8Tz3AC83YYiz9LydsLNXEZJLHY",
  "39TKsUQ5QpEL1wowc6GMUqak94ijirPuP69ooV3xsFmiKQX2dau",
  "2UEJjT3dSdwc8dAo7oedPzznXceXCEsBbDfAvSymqpqDrkZMv7JBEUpLyhkghioYAWC9W4sKysry",
  "7VmMEkphxCFSV1y659Th4dkk6x6bJS5eQvbt8rzUYKQyd6ACgwQ4vXHtXKFUwP2kW3XULipnHJdZ7",
  "tc1qdlapns4zkn03juf2k9xwwpct209suj6mgcd9gh",
  "bt1psa5eptk29c4jc9yumeseat3a0l5e2fpmw635za2p4gpwdnthueysxga9je",
  "tb13w8c43lykfj3lvm9sgp6dsnfjla3d57cm83seykunf0ltxjc9lt2q4efm4d",
  "bcrt1rjqr2tdkm",
  "bc10lyxwnxa70l270e6fcmxr4x7dtgu2yvy7gzkurwxy4zhdvgaqrrn6pfg2flyhqzy5t5se8yu3",
  "TB1QFDFM763VXVSUNZHQLPWC0Q8FG5LJX6ZN",
  "bcrt1q60chha7wfwlau4kdr4mlvyeyc8mnnh9dhxk05e0hmrxcuhghefj36uwyha",
  "bc1gmk9yu",
  "tb1ly0q7p",
  "bcrt1qdwttaw38uf42wxw40kwk3u8nguyTQH3hx6jmqp",
  "bc1qtsvlht6730n04f2mpaj5vv8hrledn5n5ug8c79",
  "tb1dclvmr",
  "bcrt1q3fqvctqu48wsvggrt09vj0yk2gzzcscdp4h98u",
  "bc1prklpq7tjcawg89cmwwqr3u5apwav36xa4zz56ady7crsllm6mpnqts7p86",
  "tb1zkm58zyhxz3ffkfgsyprflg543slsl4c4",
  "bcrt1snzr5kaypnfhpnjanrhd20fhqcjxm3hfh7dw9fu",
  "2GgnYKqBGuA2Mm5GnrPsMTZR81xPhNtgMYoFUZngZGiobhCuUpCaTriUHRcgFreEekNdPAR17q8d",
  "AZEah8d1EK362okRBS66e8SvdtYkrE8tsX",
  "gep8xr77FyPW6zYP15RiV9W8nL6w2HyHB16cUDakfyDceMA6ZzUdhJjk2LPuLYHnLkBqkRTTi6z",
  "2NDNP7GY59tTJPZTpbkprhM9SR99Nn5rUs7",
  "2Csgzy2T287YAjeU5tFtt1nPshBZAUFQi4WtgaWyZGKSBNnKXHy2Tmxo8QK4Mfdds977ShcDWC5o",
  "Kwjk3Vy6sdXMQDGWJzaWmqFxUNtWZCX1q4F4Kpt8jNNUoWJUUaTY",
  "Svj8kk98bAS9V4L2crmxakbhmnPm3cJ1tJ4Je4yVzDreU8eSTFURS1SPYv5oWEQD8Q9VBDvx5uF",
  "KNYsv6v9GtkGeD4WdQnBEJCrPKQm91PTxAbCfXr66LEd4JDmhPWC",
  "2UJ2H2xvAeXmFKfQwMyDoSdQTTPFMNCT3SsoUafBWKzoGP3NsUK1buEgQZG38viyD53jgMdpqfT7",
  "6aLMfayKF4TW4ecn5SEc8FExpyJA2peKxYRGZhes6tQ4NTTzuGy",
  "7VP4FmcebU2thJns9MnXde7LWfuqR5vMizrAuUoq2GcJjzTyA4RHFcPVdZL8PLg1SbpSFdJrvLXoY5",
  "tc1q5qdvt99uc92jyz663dtdpfpv6nr67ahmgwcpq2",
  "bt1peu3ppd7x796sjjenp09r8cs22rhylqm9lhggk72qp8q22vzft0wq2a0x6j",
  "tb1323z3lnz7dl3kd0nsuh6xy4he9almzl67anxgg3xdzkaxc9rwntlqdhdzd7",
  "bcrt1r2gc42sky",
  "bc10fd889x4hd54tqu2ewg9t4hhft2wl7m6x50av4uswzw46xe6as0xmltfg7vrjfkvm459vld7w",
  "TB1QZY7V0F2AT3308YGGNGN66ULJTCN3RY6F",
  "bcrt1qjg3cwht92znyw0l4r5rtctmls337nrc7g0ry9drjxmlecjd3atl3fake7c",
  "bc1qmgf8xt8xkecl79k04mma3lz34gqep7hg4",
  "TB1Q3F9WGNXE9ZMTTMDN5VKVKHYZ8Y0LCV72YV7V5LSXTJXEYHNHEHASLYL0TZ"]

example : keyIoInvalid.size = 70 := by native_decide

example : keyIoInvalid.all (fun text =>
    !(deriveOutputDescriptor s!"addr({text})").isOk) = true := by
  native_decide

/-! Cases from Bitcoin Core `src/test/descriptor_tests.cpp` at
df0dc1e2d2059213e49a9f115fd55a9f0119d26c. `combo()` scripts are listed in
Core's output order. -/

private def derivesScripts (descriptor : String) (scripts : List String) : Bool :=
  match deriveOutputDescriptors descriptor with
  | .ok outputs => outputs.map (·.scriptPubKey) == scripts.map hex
  | .error _ => false

-- descriptor_tests.cpp:611
example : derivesScripts "combo(L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1)"
    ["2103a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bdac",
     "76a9149a1c78a507689f6f54b847ad1cef1e614ee23f1e88ac",
     "00149a1c78a507689f6f54b847ad1cef1e614ee23f1e",
     "a91484ab21b1b2fd065d4504ff693d832434b6108d7b87"] = true := by
  native_decide

example : derivesScripts
    "combo(03a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd)"
    ["2103a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bdac",
     "76a9149a1c78a507689f6f54b847ad1cef1e614ee23f1e88ac",
     "00149a1c78a507689f6f54b847ad1cef1e614ee23f1e",
     "a91484ab21b1b2fd065d4504ff693d832434b6108d7b87"] = true := by
  native_decide

-- descriptor_tests.cpp:622
example : derivesScripts "combo(5KYZdUEo39z3FPrtuX2QbbwGnNP5zTd7yyr2SC1j299sBCnWjss)"
    ["4104a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd5b8dec5235a0fa8722476c7709c02559e3aa73aa03918ba2d492eea75abea235ac",
     "76a914b5bd079c4d57cc7fc28ecf8213a6b791625b818388ac"] = true := by
  native_decide

-- descriptor_tests.cpp:1030 rejects combo() below the top level.
example : !(deriveOutputDescriptors
    "sh(combo(L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1))").isOk = true := by
  native_decide

-- descriptor_tests.cpp:1053
example : !(deriveOutputDescriptor "addr(asdf)").isOk = true := by native_decide

-- descriptor_tests.cpp:1172 and 1174 infer these scripts as addr().
example : derivesScript "addr(17P7ge56F2QcdHxxRBa2NyzmejFggPwBJ9)"
    "76a91445ff7c2327866472639d507334a9a00119dfd32688ac" = true := by
  native_decide

example : derivesScript "addr(bc1qyt3k8ffrj3apzrv6n6c3fqsduxp6egcnk2r66j)"
    "001422e363a523947a110d9a9eb114820de183aca313" = true := by
  native_decide

end LeanMiniscript.Conformance.Descriptor
