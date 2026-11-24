/-!
# MAGLean.Sha256

Pure, zero-dependency FIPS 180-4 SHA-256 implementation in Lean 4 core (`UInt32` /
`ByteArray`) used to authenticate raw input evidence files in MAGLean QC reports.
-/

namespace MAGLean.Sha256

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

@[inline] private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] private def bigSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

@[inline] private def bigSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

@[inline] private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)

@[inline] private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

private def padMessage (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (msg.size.toUInt64) * 8
  let mut out := msg.push 0x80
  while (out.size % 64) != 56 do
    out := out.push 0x00
  for i in [0:8] do
    let shift : UInt64 := ((7 - i) * 8).toUInt64
    out := out.push ((bitLen >>> shift) &&& 0xff).toUInt8
  return out

private def readBE32 (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (bs.get! off).toUInt32
  let b1 := (bs.get! (off + 1)).toUInt32
  let b2 := (bs.get! (off + 2)).toUInt32
  let b3 := (bs.get! (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

private def compressBlock (state : Array UInt32) (bs : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    w := w.set! i (readBE32 bs (off + 4 * i))
  for i in [16:64] do
    let s0 := smallSigma0 (w[i - 15]!)
    let s1 := smallSigma1 (w[i - 2]!)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let t1 := h + bigSigma1 e + ch e f g + K[i]! + w[i]!
    let t2 := bigSigma0 a + maj a b c
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[
    state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h
  ]

private def hexDigit (n : UInt32) : Char :=
  match n.toNat with
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
  | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
  | 8  => '8' | 9  => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _  => 'f'

private def wordToHex (w : UInt32) : String := Id.run do
  let mut cs : List Char := []
  for i in [0:8] do
    let shift : UInt32 := ((7 - i) * 4).toUInt32
    cs := cs ++ [hexDigit ((w >>> shift) &&& 0xf)]
  return String.ofList cs

/-- Compute the lowercase 64-character hexadecimal SHA-256 digest of raw bytes. -/
def sha256Bytes (msg : ByteArray) : String := Id.run do
  let padded := padMessage msg
  let numBlocks := padded.size / 64
  let mut state := H0
  for blk in [0:numBlocks] do
    state := compressBlock state padded (blk * 64)
  let mut out := ""
  for i in [0:8] do
    out := out ++ wordToHex state[i]!
  return out

/-- Compute the SHA-256 hex digest of a UTF-8 string. -/
def sha256String (s : String) : String :=
  sha256Bytes s.toUTF8

end MAGLean.Sha256
