import CCLib.Integers
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# FloatLib arithmetic for the Clight semantics

Adapted from Certora CLean; see `../upstream.json` and `../LICENSE`.
The public names match the Clight exporter, but the carriers and operations
are FloatLib's pure binary32 and binary64 definitions. No native hardware
floating-point operation participates in these definitions.

Integer conversion truncates the exact finite dyadic value before checking
the destination range. Cross-format conversion uses FloatLib's nearest-even
cast. NaN propagation follows FloatLib; this substitution is not a proof of
correspondence with Rocq's CompCert/Flocq NaN policy.
-/

namespace CC.Floats

open FloatLib.Floats.Formats.BinaryInterchange

/-- The binary64 carrier used by both Clight and the numerical proof. -/
abbrev Float := Model FloatFormat.binary64

/-- The binary32 carrier used by Clight. -/
abbrev Float32 := Model FloatFormat.binary32

private def compareValues {fmt : FloatFormat} (c : Comparison)
    (x y : Model fmt) : Bool :=
  match Model.compare x y with
  | none => c == .Cne
  | some ordering =>
    match c with
    | .Ceq => ordering == .eq
    | .Cne => ordering != .eq
    | .Clt => ordering == .lt
    | .Cle => ordering != .gt
    | .Cgt => ordering == .gt
    | .Cge => ordering != .lt

/-- Truncate before checking bounds; nonfinite values have no integer result. -/
private def toInteger? {fmt : FloatFormat} (x : Model fmt) (lo hi : Z) : Option Z := do
  let value ← Model.toDyadic? x
  let n := Model.roundDyadicToInt .towardZero value
  if lo ≤ n ∧ n ≤ hi then some n else none

private def ofInteger (fmt : FloatFormat) (n : Z) : Model fmt :=
  Model.roundDyadic fmt
    { negative := decide (n < 0), significand := n.natAbs, exponent := 0 }

namespace Float

def ofBits (b : Integers.Int64) : Float := Model.ofBits b
def toBits (f : Float) : Integers.Int64 := Model.toBits f
def zero : Float := Model.ofNatBits 0
def neg (f : Float) : Float := Model.neg f
def abs (f : Float) : Float := Model.abs f
def add (x y : Float) : Float := Model.add x y
def sub (x y : Float) : Float := Model.sub x y
def mul (x y : Float) : Float := Model.mul x y
def div (x y : Float) : Float := Model.div x y
def isNaN (f : Float) : Bool := Model.isNaN f
def cmp (c : Comparison) (x y : Float) : Bool := compareValues c x y

def toInt (f : Float) : Option Integers.Int :=
  (toInteger? f Integers.Int.min_signed Integers.Int.max_signed).map Integers.Int.repr

def toIntu (f : Float) : Option Integers.Int :=
  (toInteger? f 0 Integers.Int.max_unsigned).map Integers.Int.repr

def toLong (f : Float) : Option Integers.Int64 :=
  (toInteger? f Integers.Int64.min_signed Integers.Int64.max_signed).map Integers.Int64.repr

def toLongu (f : Float) : Option Integers.Int64 :=
  (toInteger? f 0 Integers.Int64.max_unsigned).map Integers.Int64.repr

def ofInt (n : Integers.Int) : Float :=
  ofInteger FloatFormat.binary64 (Integers.Int.signed n)

def ofIntu (n : Integers.Int) : Float :=
  ofInteger FloatFormat.binary64 (Integers.Int.unsigned n)

def ofLong (n : Integers.Int64) : Float :=
  ofInteger FloatFormat.binary64 (Integers.Int64.signed n)

def ofLongu (n : Integers.Int64) : Float :=
  ofInteger FloatFormat.binary64 (Integers.Int64.unsigned n)

end Float

namespace Float32

def ofBits (b : Integers.Int) : Float32 := Model.ofBits b
def toBits (f : Float32) : Integers.Int := Model.toBits f
def zero : Float32 := Model.ofNatBits 0
def neg (f : Float32) : Float32 := Model.neg f
def abs (f : Float32) : Float32 := Model.abs f
def add (x y : Float32) : Float32 := Model.add x y
def sub (x y : Float32) : Float32 := Model.sub x y
def mul (x y : Float32) : Float32 := Model.mul x y
def div (x y : Float32) : Float32 := Model.div x y
def isNaN (f : Float32) : Bool := Model.isNaN f
def cmp (c : Comparison) (x y : Float32) : Bool := compareValues c x y

def toInt (f : Float32) : Option Integers.Int :=
  (toInteger? f Integers.Int.min_signed Integers.Int.max_signed).map Integers.Int.repr

def toIntu (f : Float32) : Option Integers.Int :=
  (toInteger? f 0 Integers.Int.max_unsigned).map Integers.Int.repr

def toLong (f : Float32) : Option Integers.Int64 :=
  (toInteger? f Integers.Int64.min_signed Integers.Int64.max_signed).map Integers.Int64.repr

def toLongu (f : Float32) : Option Integers.Int64 :=
  (toInteger? f 0 Integers.Int64.max_unsigned).map Integers.Int64.repr

def ofInt (n : Integers.Int) : Float32 :=
  ofInteger FloatFormat.binary32 (Integers.Int.signed n)

def ofIntu (n : Integers.Int) : Float32 :=
  ofInteger FloatFormat.binary32 (Integers.Int.unsigned n)

def ofLong (n : Integers.Int64) : Float32 :=
  ofInteger FloatFormat.binary32 (Integers.Int64.signed n)

def ofLongu (n : Integers.Int64) : Float32 :=
  ofInteger FloatFormat.binary32 (Integers.Int64.unsigned n)

end Float32

def Float.ofSingle (f : Float32) : Float :=
  Model.cast FloatFormat.binary32 FloatFormat.binary64 f

def Float.toSingle (f : Float) : Float32 :=
  Model.cast FloatFormat.binary64 FloatFormat.binary32 f

end CC.Floats
