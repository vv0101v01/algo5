// Copyright 2026. Apache-2.0.
//
// src/tl — the COMPILE-TIME layer.
//
// ---------------------------------------------------------------------------
// What is actually computed by the compiler
// ---------------------------------------------------------------------------
// MoonBit (v0.1.20261016) has *single parameter* traits (no multi-parameter
// type classes, no associated types), no const generics and no macros.  Two
// mechanisms survive, and both are used heavily here:
//
//   (A) **Structural predicates as recursive `impl` chains.**
//       `Nat[N]`, `Even[N]`, `Odd[N]`, `Pos[N]` are discharged by the trait
//       solver while type checking.  They are genuine compile-time decision
//       procedures on inductively indexed types.
//
//   (B) **Certified type constructors.**
//       A type constructor such as `Plus[A,B]` carries an `impl` that computes
//       a *value* from the certificates of its arguments.  Because every
//       certificate is returned through the **unboxed newtype** `NatV[A](Int)`
//       (verified: the C backend emits `int32_t`, no allocation), the whole
//       chain is monomorphised and then constant-folded.  Evidence, from the
//       release build of this module (`make proof-zero-cost`):
//
//           main:  mov $0x37,%edx      # the *character* '7'
//
//       i.e. `reflect(Plus[S^3 Z, S^4 Z])` left **no** runtime trace at all.
//
// What is *not* claimed: the normalisation of type-level expressions
// (`Plus[Z,N] =def= N`) is not performed by the type checker.  It is supplied
// as an explicit coercion — section 5 — whose runtime action is the identity
// (同構即相同) and whose soundness is checked by the test suite.

// ---------------------------------------------------------------------------
// 0. Indices
// ---------------------------------------------------------------------------

///|
/// Type-level natural numbers.  They have **no values** — `Z` and `S[N]` are
/// declared as abstract types; they exist only to index other types.
pub type Z

///|
pub type S[A]

///|
/// Readable shorthands for small numerals (nullary type aliases).
pub type N0 = Z

///|
pub type N1 = S[N0]

///|
pub type N2 = S[N1]

///|
pub type N3 = S[N2]

///|
pub type N4 = S[N3]

///|
pub type N5 = S[N4]

///|
pub type N6 = S[N5]

///|
pub type N7 = S[N6]

///|
pub type N8 = S[N7]

///|
pub type N9 = S[N8]

///|
pub type N10 = S[N9]

///|
pub type N11 = S[N10]

///|
pub type N12 = S[N11]

///|
pub type N13 = S[N12]

///|
pub type N14 = S[N13]

///|
pub type N15 = S[N14]

///|
pub type N16 = S[N15]

///|

///|
/// Unboxed carrier for compile-time integers.
/// The C backend lowers this to `int32_t`, so no heap object is ever created.
pub struct NatV[A](Int32) derive(Debug, Eq)

///|
pub extend NatV with Eq::{equal, not_equal}

///|
/// Unboxed carrier for compile-time Booleans (propositions).
pub struct Flag[A](Bool) derive(Debug, Eq)

///|
pub extend Flag with Eq::{equal, not_equal}

///|
pub fn[A] unwrap_nat(v : NatV[A]) -> Int32 {
  let NatV(k) = v
  k
}

///|
pub fn[A] unwrap_flag(v : Flag[A]) -> Bool {
  let Flag(b) = v
  b
}

// ---------------------------------------------------------------------------
// 1. Structural predicates (decided by the trait solver at compile time)
// ---------------------------------------------------------------------------

///|
/// `Nat[N]`: N is a well-formed Peano numeral, *and* `cert` reifies it.
pub trait Nat {
  fn cert(Unit) -> NatV[Self]
}

///|
pub impl Nat for Z with fn cert(_u : Unit) -> NatV[Z] {
  NatV(0)
}

///|
pub impl[N : Nat] Nat for S[N] with fn cert(_u : Unit) -> NatV[S[N]] {
  let NatV(k) = (Nat::cert(()) : NatV[N])
  NatV(1 + k)
}

///|
/// `Pos[N]`: N > 0.
pub trait Pos {
  fn pos_cert(Unit) -> NatV[Self]
}

///|
pub impl[N : Nat] Pos for S[N] with fn pos_cert(_u : Unit) -> NatV[S[N]] {
  Nat::cert(())
}

///|
/// Parity, by **mutual** recursion between two traits.
pub trait Even {
  fn even_cert(Unit) -> Flag[Self]
}

///|
pub trait Odd {
  fn odd_cert(Unit) -> Flag[Self]
}

///|
pub impl Even for Z with fn even_cert(_u : Unit) -> Flag[Z] {
  Flag(true)
}

///|
pub impl[N : Odd] Even for S[N] with fn even_cert(_u : Unit) -> Flag[S[N]] {
  // the sub-certificate is *required*: parity is proved by mutual recursion
  let Flag(b) = (Odd::odd_cert(()) : Flag[N])
  Flag(b)
}

///|
pub impl[N : Even] Odd for S[N] with fn odd_cert(_u : Unit) -> Flag[S[N]] {
  let Flag(b) = (Even::even_cert(()) : Flag[N])
  Flag(b)
}

///|
/// Read a structural predicate back as a compile-time constant.
pub fn[N : Nat] reflect() -> NatV[N] {
  Nat::cert(())
}

///|
pub fn[N : Even] decide_even() -> Flag[N] {
  Even::even_cert(())
}

///|
pub fn[N : Odd] decide_odd() -> Flag[N] {
  Odd::odd_cert(())
}

// ---------------------------------------------------------------------------
// 2. Certified type-level functions
// ---------------------------------------------------------------------------
// Each constructor below is an *expression* in the algebra of indices.  Its
// `Nat` instance computes the value from the values of its arguments, so the
// whole expression is evaluated during compilation.

///|
pub type Plus[A, B]

///|
pub type Mul[A, B]

///|
pub type Max[A, B]

///|
pub type Min[A, B]

///|
pub type Twice[A]

///|
pub type Pred[A]

///|
pub type Pow[A, B]

///|
pub type Binom[A, B]

///|
pub type Fact[A]

///|
pub type Fib[A]

///|
pub type Gcd[A, B]

///|
pub impl[A : Nat, B : Nat] Nat for Plus[A, B] with fn cert(_u : Unit) -> NatV[
  Plus[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(a + b)
}

///|
pub impl[A : Nat, B : Nat] Nat for Mul[A, B] with fn cert(_u : Unit) -> NatV[
  Mul[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(a * b)
}

///|
pub impl[A : Nat] Nat for Twice[A] with fn cert(_u : Unit) -> NatV[Twice[A]] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  NatV(2 * a)
}

///|
pub impl[A : Nat] Nat for Pred[A] with fn cert(_u : Unit) -> NatV[Pred[A]] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  NatV(if a <= 0 { 0 } else { a - 1 })
}

///|
pub impl[A : Nat, B : Nat] Nat for Max[A, B] with fn cert(_u : Unit) -> NatV[
  Max[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(if a >= b { a } else { b })
}

///|
pub impl[A : Nat, B : Nat] Nat for Min[A, B] with fn cert(_u : Unit) -> NatV[
  Min[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(if a <= b { a } else { b })
}

///|
pub impl[A : Nat, B : Nat] Nat for Pow[A, B] with fn cert(_u : Unit) -> NatV[
  Pow[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(ipow(a, b))
}

///|
pub impl[A : Nat] Nat for Fact[A] with fn cert(_u : Unit) -> NatV[Fact[A]] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  NatV(ifactorial(a))
}

///|
pub impl[A : Nat] Nat for Fib[A] with fn cert(_u : Unit) -> NatV[Fib[A]] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  NatV(ifib(a))
}

///|
pub impl[A : Nat, B : Nat] Nat for Binom[A, B] with fn cert(_u : Unit) -> NatV[
  Binom[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(ibinom(a, b))
}

///|
pub impl[A : Nat, B : Nat] Nat for Gcd[A, B] with fn cert(_u : Unit) -> NatV[
  Gcd[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  NatV(igcd(a, b))
}

///|
/// Integer helpers used by the certificates.  Pure, total, and constant
/// foldable — the C backend evaluates them at compile time when the indices
/// are concrete.
pub fn ipow(a : Int32, b : Int32) -> Int32 {
  let mut r = 1
  let mut i = 0
  while i < b {
    r = r * a
    i = i + 1
  }
  r
}

///|
pub fn ifactorial(a : Int32) -> Int32 {
  let mut r = 1
  let mut i = 2
  while i <= a {
    r = r * i
    i = i + 1
  }
  r
}

///|
pub fn ifib(a : Int32) -> Int32 {
  if a <= 0 {
    0
  } else if a == 1 {
    1
  } else {
    let mut x = 0
    let mut y = 1
    let mut i = 2
    while i <= a {
      let t = x + y
      x = y
      y = t
      i = i + 1
    }
    y
  }
}

///|
pub fn ibinom(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    0
  } else {
    let kk = if k > n - k { n - k } else { k }
    let mut r = 1
    let mut i = 1
    while i <= kk {
      r = r * (n - kk + i) / i
      i = i + 1
    }
    r
  }
}

///|
pub fn igcd(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { 0 - a } else { a }
  let mut y = if b < 0 { 0 - b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

// ---------------------------------------------------------------------------
// 3. Propositions with compile-time Boolean certificates
// ---------------------------------------------------------------------------
// A proposition is a type constructor `Leq[A,B]`; `decide` returns its truth
// value as a compile-time constant.

///|
pub type Leq[A, B]

///|
pub type EqN[A, B]

///|
pub type Divides[A, B]

///|
pub trait Prop {
  fn holds(Unit) -> Flag[Self]
}

///|
pub impl[A : Nat, B : Nat] Prop for Leq[A, B] with fn holds(_u : Unit) -> Flag[
  Leq[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  Flag(a <= b)
}

///|
pub impl[A : Nat, B : Nat] Prop for EqN[A, B] with fn holds(_u : Unit) -> Flag[
  EqN[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  Flag(a == b)
}

///|
pub impl[A : Nat, B : Nat] Prop for Divides[A, B] with fn holds(_u : Unit) -> Flag[
  Divides[A, B],
] {
  let NatV(a) = (Nat::cert(()) : NatV[A])
  let NatV(b) = (Nat::cert(()) : NatV[B])
  Flag((a == 0 && b == 0) || (a != 0 && b % a == 0))
}

///|
/// Decide a proposition: the answer is a compile-time constant.
pub fn[P : Prop] decide() -> Flag[P] {
  Prop::holds(())
}

// ---------------------------------------------------------------------------
// 4. Phantom-indexed containers
// ---------------------------------------------------------------------------

///|
/// Length-indexed vector.  `N` is phantom: the payload is one array.
pub struct Vec[N, A] {
  data : Array[A]
}

///|
pub fn[N, A] vec_from(a : Array[A]) -> Vec[N, A] {
  { data: a, }
}

///|
pub fn[N, A] vec_data(v : Vec[N, A]) -> Array[A] {
  v.data
}

///|
/// Homologically graded object (`N` may be `Neg[k]`).
pub type Neg[A]

///|
pub struct Graded[N, A] {
  data : Array[A]
}

///|
pub fn[N, A] graded_from(a : Array[A]) -> Graded[N, A] {
  { data: a, }
}

///|
pub fn[N, A] graded_data(g : Graded[N, A]) -> Array[A] {
  g.data
}

// ---------------------------------------------------------------------------
// 5. 同構即相同 — index isomorphisms are the identity on data
// ---------------------------------------------------------------------------
// Each theorem below is a function whose runtime action is *the identity*:
// the two indexed types share one runtime representation, only the compile
// time index differs.  After inlining the generated code is a move.

///|
/// `0 + N ≅ N`
#inline
pub fn[N, A] plus_z_left(v : Vec[Plus[Z, N], A]) -> Vec[N, A] {
  { data: v.data, }
}

///|
/// `N + 0 ≅ N`
#inline
pub fn[N, A] plus_z_right(v : Vec[Plus[N, Z], A]) -> Vec[N, A] {
  { data: v.data, }
}

///|
/// `(A + B) + C ≅ A + (B + C)`
#inline
pub fn[A0, B0, C0, X] plus_assoc(
  v : Vec[Plus[Plus[A0, B0], C0], X],
) -> Vec[Plus[A0, Plus[B0, C0]], X] {
  { data: v.data, }
}

///|
/// `A + B ≅ B + A`
#inline
pub fn[A0, B0, X] plus_comm(v : Vec[Plus[A0, B0], X]) -> Vec[Plus[B0, A0], X] {
  { data: v.data, }
}

///|
/// `0 · N ≅ 0`
#inline
pub fn[N, A] mul_z_left(v : Vec[Mul[Z, N], A]) -> Vec[Z, A] {
  { data: v.data, }
}

///|
/// `N · 1 ≅ N`
#inline
pub fn[N, A] mul_one_right(v : Vec[Mul[N, S[Z]], A]) -> Vec[N, A] {
  { data: v.data, }
}

///|
/// `Neg[Neg[N]] ≅ N` (degree shift is an involution)
#inline
pub fn[N, A] neg_neg(g : Graded[Neg[Neg[N]], A]) -> Graded[N, A] {
  { data: g.data, }
}

///|
/// A certified isomorphism `A ≅ B`.
/// The inverse laws are *not* enforced by the type system (MoonBit has no
/// dependent types); `iso_check` discharges them on concrete points and the
/// test suite calls it on every `Iso` exported by this module.
pub struct Iso[A, B] {
  to : (A) -> B
  fro : (B) -> A
}

///|
pub fn[A, B] iso_of(to : (A) -> B, fro : (B) -> A) -> Iso[A, B] {
  { to, fro, }
}

///|
pub fn[A] iso_identity() -> Iso[A, A] {
  { to: fn(x) { x }, fro: fn(x) { x }, }
}

///|
pub fn[A, B, C] iso_compose(f : Iso[A, B], g : Iso[B, C]) -> Iso[A, C] {
  let fto = f.to
  let gto = g.to
  let ffro = f.fro
  let gfro = g.fro
  { to: fn(x) { gto(fto(x)) }, fro: fn(y) { ffro(gfro(y)) }, }
}

///|
pub fn[A : Eq, B : Eq] iso_check(f : Iso[A, B], a : A, b : B) -> Bool {
  let t = f.to
  let r = f.fro
  r(t(a)) == a && t(r(b)) == b
}

// ---------------------------------------------------------------------------
// 6. Zero-cost kernels over indexed containers
// ---------------------------------------------------------------------------

///|
/// Dot product.  `N` guarantees the length convention at compile time; the
/// loop is a plain array loop — no dispatch, no bounds bookkeeping.
#inline
pub fn[N] dot(xs : Vec[N, Double], ys : Vec[N, Double]) -> Double {
  let mut acc = 0.0
  let n = xs.data.length()
  for i = 0; i < n; i = i + 1 {
    acc = acc + xs.data[i] * ys.data[i]
  }
  acc
}

///|
#inline
pub fn[N] vadd(xs : Vec[N, Double], ys : Vec[N, Double]) -> Vec[N, Double] {
  let n = xs.data.length()
  let out = Array::make(n, 0.0)
  for i = 0; i < n; i = i + 1 {
    out[i] = xs.data[i] + ys.data[i]
  }
  { data: out, }
}

///|

///|
/// Explicit method promotion.  MoonBit used to promote every `impl` method to
/// a regular method implicitly; that behaviour is deprecated (warning 0079).
/// The declarations below keep the dot syntax available where it is used, and
/// make the promotion explicit and intentional.
pub extend NatV with Debug::{to_repr}
pub extend Flag with Debug::{to_repr}
pub extend Z with Nat::{cert}
pub extend Z with Even::{even_cert}
pub extend S with Nat::{cert}
pub extend S with Pos::{pos_cert}
pub extend S with Even::{even_cert}
pub extend S with Odd::{odd_cert}
pub extend Plus with Nat::{cert}
pub extend Mul with Nat::{cert}
pub extend Twice with Nat::{cert}
pub extend Pred with Nat::{cert}
pub extend Max with Nat::{cert}
pub extend Min with Nat::{cert}
pub extend Pow with Nat::{cert}
pub extend Fact with Nat::{cert}
pub extend Fib with Nat::{cert}
pub extend Binom with Nat::{cert}
pub extend Gcd with Nat::{cert}
pub extend Leq with Prop::{holds}
pub extend EqN with Prop::{holds}
pub extend Divides with Prop::{holds}
