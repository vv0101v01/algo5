/// 值 (VALUED FIELDS) — non-Archimedean analysis, machine-checked.
///
/// Definitions
/// -----------
/// A *(Krull) valuation* on a field K is a map v : K^× → Γ onto an ordered
/// abelian group Γ (extended by v(0) = ∞) with
///
///     (V1)  v(x y) = v(x) + v(y)
///     (V2)  v(x + y) ≥ min( v(x), v(y) )          (ultrametric inequality)
///
/// It induces the *non-Archimedean absolute value* |x| = c^{−v(x)} (any
/// 0 < c < 1; we take c = 1/p resp. c = e) which satisfies
///
///     (N1)  |x| = 0 ⟺ x = 0
///     (N2)  |x y| = |x| · |y|
///     (N3)  |x + y| ≤ max( |x|, |y| )             (strong triangle inequality)
///
/// Attached to v are the *valuation ring* O_v = {x : v(x) ≥ 0}, its maximal
/// ideal m_v = {x : v(x) > 0} and the *residue field* k(v) = O_v / m_v.
///
/// For K = Q and a prime p, v = v_p is the exponent of p in the
/// factorisation; |·|_p is the p-adic absolute value and ∞ denotes the usual
/// archimedean one.
///
/// Theorems implemented here
/// -------------------------
/// T1 (Ostrowski / product formula).  For x ∈ Q^×,
///         |x|_∞ · Π_p |x|_p = 1 ,
/// the product being over all primes (all but finitely many factors are 1).
/// Equivalently Π_p p^{−v_p(x)} = 1/|x|_∞.
/// T2 (Strong triangle inequality).  |x + y|_p ≤ max(|x|_p, |y|_p), with
/// equality unless v_p(x) ≠ v_p(y); in particular the p-adic metric is an
/// ultrametric and every triangle is isosceles.
/// T3 (Hensel's lemma, simple root).  If f ∈ Z_p[x], f(a) ≡ 0 (mod p) and
/// f'(a) ≢ 0 (mod p), then a lifts uniquely to a root in Z_p; Newton
/// iteration a ← a − f(a)/f'(a) converges quadratically:
/// f(a_k) ≡ 0 (mod p^k) ⇒ f(a_k − f(a_k)/f'(a_k)) ≡ 0 (mod p^{2k}).
/// T4 (Hensel's lemma, factorisation).  If f ≡ g₀ h₀ (mod p) with g₀, h₀
/// monic and coprime mod p, then f = g h in Z_p[x] with g ≡ g₀, h ≡ h₀.
/// T5 (Newton polygon).  For f = Σ a_i x^i ∈ Q_p[x] let N(f) be the lower
/// convex hull of the points (i, v_p(a_i)).  If N(f) has a segment of
/// horizontal length m and slope −s, then f has exactly m roots (with
/// multiplicity, in Q̄_p) of valuation s.  In particular
///         #{roots of valuation s} = m      and      v(a₀) − v(a_d) = Σ (roots' valuations)·(−slopes).
/// T6 (Valuation ring).  O = {x : v(x) ≥ 0} is a ring, m = {x : v(x) > 0} is
/// its unique maximal ideal, O^× = {x : v(x) = 0} = O ∖ m, and
/// k(v) = O/m ≅ F_p : the reduction map is a surjective ring homomorphism and
/// a unit of O reduces to a non-zero element of F_p.

///|
/// Integer power a^n for n >= 0.  Delegates to `@tl.ipow`: one
/// implementation, shared by every package in the module.
pub fn ipow(a : Int32, n : Int32) -> Int32 {
  @tl.ipow(a, n)
}

///|
/// Modular addition: (a + b) mod m, with 0 <= a, b < m and 2m < 2^31.
pub fn addmod(a : Int32, b : Int32, m : Int32) -> Int32 {
  let s = a + b
  if s >= m {
    s - m
  } else {
    s
  }
}

///|
/// Modular multiplication by repeated doubling.  Necessary because the
/// intermediate a·b can overflow even when the result fits: all p-adic
/// arithmetic here works modulo m = p^N with m < 2^30, so 2m < 2^31.
pub fn mulmod(a0 : Int32, b0 : Int32, m : Int32) -> Int32 {
  let mut a = @nf.mod_pos(a0, m)
  let mut b = @nf.mod_pos(b0, m)
  let mut r = 0
  while b > 0 {
    if b % 2 == 1 {
      r = addmod(r, a, m)
    }
    a = addmod(a, a, m)
    b = b / 2
  }
  r
}

///|
pub fn is_prime(n : Int32) -> Bool {
  if n < 2 {
    return false
  }
  let mut d = 2
  while d * d <= n {
    if n % d == 0 {
      return false
    }
    d = d + 1
  }
  true
}

///|
pub fn primes_upto(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut k = 2
  while k <= n {
    if is_prime(k) {
      out.push(k)
    }
    k = k + 1
  }
  out
}

///|
/// The p-adic valuation of a non-zero integer: the exponent of p in n.
pub fn padic_val_z(n : Int32, p : Int32) -> Int32 {
  if n == 0 {
    abort("padic_val_z: v(0) is infinite")
  }
  let mut m = if n < 0 { 0 - n } else { n }
  let mut k = 0
  while m % p == 0 {
    m = m / p
    k = k + 1
  }
  k
}

///|
/// The p-adic valuation of the rational num/den (both non-zero).
pub fn padic_val_q(num : Int32, den : Int32, p : Int32) -> Int32 {
  padic_val_z(num, p) - padic_val_z(den, p)
}

///|
/// The p-adic absolute value |x|_p = p^{−v_p(x)}, as a Double.
pub fn padic_norm(num : Int32, den : Int32, p : Int32) -> Double {
  let v = padic_val_q(num, den, p)
  if v >= 0 {
    1.0 / ipow(p, v).to_double()
  } else {
    ipow(p, 0 - v).to_double()
  }
}

///|
/// The archimedean absolute value.
pub fn arch_norm(num : Int32, den : Int32) -> Double {
  let a = if num < 0 { 0 - num } else { num }
  a.to_double() / den.to_double()
}

///|
/// T1: |x|_∞ · Π_{p ≤ bound} |x|_p.  Equals 1 as soon as `bound` exceeds
/// every prime dividing num·den (Ostrowski's product formula).
pub fn product_formula(num : Int32, den : Int32, bound : Int32) -> Double {
  let mut acc = arch_norm(num, den)
  for p in primes_upto(bound) {
    acc = acc * padic_norm(num, den, p)
  }
  acc
}

///|
/// T1 in exact rational arithmetic: returns (numerator, denominator) of
/// Π_{p ≤ bound} |x|_p, so the product formula says num·P = den.
pub fn padic_norm_product(
  num : Int32,
  den : Int32,
  bound : Int32,
) -> (Int32, Int32) {
  let mut n : Int32 = 1
  let mut d : Int32 = 1
  for p in primes_upto(bound) {
    let v = padic_val_q(num, den, p)
    if v > 0 {
      d = d * ipow(p, v)
    } else if v < 0 {
      n = n * ipow(p, 0 - v)
    }
  }
  (n, d)
}

///|
/// T2: the strong triangle inequality |x + y|_p ≤ max(|x|_p, |y|_p).
/// Returns (|x|, |y|, |x+y|) so that the caller can also test the
/// "isosceles" refinement: equality holds unless v_p(x) ≠ v_p(y).
pub fn ultrametric_triple(
  n1 : Int32,
  d1 : Int32,
  n2 : Int32,
  d2 : Int32,
  p : Int32,
) -> (Double, Double, Double) {
  let x = padic_norm(n1, d1, p)
  let y = padic_norm(n2, d2, p)
  let s = padic_norm(n1 * d2 + n2 * d1, d1 * d2, p)
  (x, y, s)
}

// ---------------------------------------------------------------------------
// Truncated p-adic arithmetic: elements of Z / p^N, kept in [0, p^N).
// ---------------------------------------------------------------------------

///|
pub fn padic_prec(p : Int32, n : Int32) -> Int32 {
  ipow(p, n)
}

///|
pub fn padic_reduce(a : Int32, p : Int32, n : Int32) -> Int32 {
  @nf.mod_pos(a, padic_prec(p, n))
}

///|
pub fn padic_add(a : Int32, b : Int32, p : Int32, n : Int32) -> Int32 {
  padic_reduce(a + b, p, n)
}

///|
pub fn padic_sub(a : Int32, b : Int32, p : Int32, n : Int32) -> Int32 {
  padic_reduce(a - b, p, n)
}

///|
pub fn padic_mul(a : Int32, b : Int32, p : Int32, n : Int32) -> Int32 {
  mulmod(a, b, padic_prec(p, n))
}

///|
pub fn padic_neg(a : Int32, p : Int32, n : Int32) -> Int32 {
  padic_reduce(0 - a, p, n)
}

///|
pub fn is_unit(a : Int32, p : Int32) -> Bool {
  @nf.mod_pos(a, p) != 0
}

///|
/// Inverse in Z/p^N; exists iff p ∤ a (i.e. v_p(a) = 0).
pub fn padic_inv(a : Int32, p : Int32, n : Int32) -> Int32 {
  let m = padic_prec(p, n)
  let (g, s, _) = @nf.ext_gcd(@nf.mod_pos(a, m), m)
  if g != 1 {
    abort("padic_inv: not a unit")
  }
  @nf.mod_pos(s, m)
}

///|
pub fn padic_pow(a : Int32, k : Int32, p : Int32, n : Int32) -> Int32 {
  let mut r = 1
  let mut i = 0
  while i < k {
    r = padic_mul(r, a, p, n)
    i = i + 1
  }
  r
}

// ---------------------------------------------------------------------------
// Polynomials over Z (dense, coefficient i is the coefficient of x^i).
// ---------------------------------------------------------------------------

///|
pub fn poly_eval(cs : Array[Int32], x : Int32) -> Int32 {
  let mut acc = 0
  let mut i = cs.length() - 1
  while i >= 0 {
    acc = acc * x + cs[i]
    i = i - 1
  }
  acc
}

///|
/// Horner evaluation modulo m (overflow-free: every step is a mulmod).
pub fn poly_eval_mod(cs : Array[Int32], x : Int32, m : Int32) -> Int32 {
  let xm = @nf.mod_pos(x, m)
  let mut acc = 0
  let mut i = cs.length() - 1
  while i >= 0 {
    acc = addmod(mulmod(acc, xm, m), @nf.mod_pos(cs[i], m), m)
    i = i - 1
  }
  acc
}

///|
pub fn poly_deriv(cs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 1; i < cs.length(); i = i + 1 {
    out.push(cs[i] * i)
  }
  if out.length() == 0 {
    out.push(0)
  }
  out
}

///|
pub fn poly_add(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    out.push(x + y)
  }
  out
}

///|
pub fn poly_sub(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    out.push(x - y)
  }
  out
}

///|
pub fn poly_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  if a.length() == 0 || b.length() == 0 {
    return [0]
  }
  let out : Array[Int32] = Array::make(a.length() + b.length() - 1, 0)
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < b.length(); j = j + 1 {
      out[i + j] = out[i + j] + a[i] * b[j]
    }
  }
  out
}

///|
/// Multiplication of polynomials over Z/m (overflow-free).
pub fn poly_mul_mod(
  a : Array[Int32],
  b : Array[Int32],
  m : Int32,
) -> Array[Int32] {
  if a.length() == 0 || b.length() == 0 {
    return [0]
  }
  let out : Array[Int32] = Array::make(a.length() + b.length() - 1, 0)
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < b.length(); j = j + 1 {
      out[i + j] = addmod(out[i + j], mulmod(a[i], b[j], m), m)
    }
  }
  out
}

///|
/// Reduce all coefficients modulo m into [0, m), dropping leading zeros.
pub fn poly_mod(cs : Array[Int32], m : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 0; i < cs.length(); i = i + 1 {
    out.push(@nf.mod_pos(cs[i], m))
  }
  poly_trim(out)
}

///|
pub fn poly_trim(cs : Array[Int32]) -> Array[Int32] {
  if cs.length() == 0 {
    return [0]
  }
  let mut k = cs.length()
  while k > 1 && cs[k - 1] == 0 {
    k = k - 1
  }
  let out : Array[Int32] = []
  for i = 0; i < k; i = i + 1 {
    out.push(cs[i])
  }
  out
}

///|
pub fn poly_deg(cs : Array[Int32]) -> Int32 {
  poly_trim(cs).length() - 1
}

// ---------------------------------------------------------------------------
// T3: Hensel lifting of a simple root.
// ---------------------------------------------------------------------------

///|
/// Is a0 a *simple* root of f modulo p, i.e. f(a0) ≡ 0 and f'(a0) ≢ 0 (mod p)?
pub fn hensel_is_simple(cs : Array[Int32], p : Int32, a0 : Int32) -> Bool {
  let f = poly_eval(cs, a0)
  let df = poly_eval(poly_deriv(cs), a0)
  @nf.mod_pos(f, p) == 0 && @nf.mod_pos(df, p) != 0
}

///|
/// T3.  Lift a simple root a0 of f mod p to a root of f modulo p^prec by the
/// Newton iteration a ← a − f(a)·f'(a)^{−1}.  The precision doubles at every
/// step (quadratic convergence), and the lift is *unique* modulo p^prec.
pub fn hensel_lift(
  cs : Array[Int32],
  p : Int32,
  a0 : Int32,
  prec : Int32,
) -> Int32 {
  if !hensel_is_simple(cs, p, a0) {
    abort("hensel_lift: not a simple root modulo p")
  }
  let dfs = poly_deriv(cs)
  let mut a = @nf.mod_pos(a0, p)
  let mut k = 1
  let mut steps = 0
  while k < prec && steps < 1000 {
    steps = steps + 1
    let k2 = if 2 * k > prec { prec } else { 2 * k }
    let m = padic_prec(p, k2)
    let fv = poly_eval_mod(cs, a, m)
    let dv = poly_eval_mod(dfs, a, m)
    let dinv = padic_inv(dv, p, k2)
    a = @nf.mod_pos(a - mulmod(fv, dinv, m), m)
    k = k2
  }
  a
}

///|
/// The residual polynomial f mod p^k, used to certify Hensel lifts.
pub fn poly_mod_pk(cs : Array[Int32], p : Int32, k : Int32) -> Array[Int32] {
  poly_mod(cs, padic_prec(p, k))
}

// ---------------------------------------------------------------------------
// T4: Hensel lifting of a factorisation (coprime factors mod p).
// ---------------------------------------------------------------------------

///|
/// Polynomial division by a monic polynomial, over Z/m.
pub fn poly_divmod_mod(
  a : Array[Int32],
  b : Array[Int32],
  m : Int32,
) -> (Array[Int32], Array[Int32]) {
  if a.length() == 0 || b.length() == 0 {
    return ([0], [0])
  }
  let r : Array[Int32] = []
  for i = 0; i < a.length(); i = i + 1 {
    r.push(@nf.mod_pos(a[i], m))
  }
  let db = poly_deg(b)
  let q : Array[Int32] = Array::make(
    if r.length() - db > 0 {
      r.length() - db
    } else {
      0
    },
    0,
  )
  let mut i = r.length() - 1
  while i >= db && db >= 0 {
    let c = @nf.mod_pos(r[i], m)
    if c != 0 {
      q[i - db] = c
      for j = 0; j <= db; j = j + 1 {
        r[i - db + j] = @nf.mod_pos(r[i - db + j] - mulmod(c, b[j], m), m)
      }
    }
    i = i - 1
  }
  (poly_trim(q), poly_trim(r))
}

///|
/// Bezout data (s, t) with s·g + t·h ≡ 1 (mod p^k), deg s < deg h,
/// assuming g, h are monic and coprime modulo p.  Built by Newton iteration
/// u ← u(2 − u) starting from the mod-p Bezout data.
fn bezout_lift(
  g : Array[Int32],
  h : Array[Int32],
  p : Int32,
  k : Int32,
) -> (Array[Int32], Array[Int32]) {
  let mut s = poly_bezout_modp(g, h, p).0
  let mut t = poly_bezout_modp(g, h, p).1
  let mut prec = 1
  let mut steps = 0
  while prec < k && steps < 200 {
    steps = steps + 1
    let nk = if 2 * prec > k { k } else { 2 * prec }
    let m = padic_prec(p, nk)
    // u = s*g + t*h  (mod m), then (s,t) <- (s*(2-u), t*(2-u))
    let u = poly_mod(poly_add(poly_mul_mod(s, g, m), poly_mul_mod(t, h, m)), m)
    let two : Array[Int32] = [2]
    let w = poly_mod(poly_sub(two, u), m)
    s = poly_mod(poly_mul_mod(s, w, m), m)
    t = poly_mod(poly_mul_mod(t, w, m), m)
    // keep the degrees bounded: reduce s modulo h and t modulo g
    let (_, rs) = poly_divmod_mod(s, h, m)
    s = rs
    let (_, rt) = poly_divmod_mod(t, g, m)
    t = rt
    prec = nk
  }
  (s, t)
}

///|
/// Extended Euclid for polynomials over the field F_p; returns (s, t) with
/// s·g + t·h ≡ 1 (mod p), assuming g, h are coprime modulo p.  The divisor is
/// normalised to be monic at every step (F_p is a field), which is what makes
/// the division terminate.
fn poly_bezout_modp(
  g0 : Array[Int32],
  h0 : Array[Int32],
  p : Int32,
) -> (Array[Int32], Array[Int32]) {
  let mut r0 = poly_mod(g0, p)
  let mut r1 = poly_mod(h0, p)
  let mut s0 : Array[Int32] = [1]
  let mut s1 : Array[Int32] = []
  let mut t0 : Array[Int32] = []
  let mut t1 : Array[Int32] = [1]
  let mut steps = 0
  while poly_deg(r1) > 0 || r1[0] != 0 {
    steps = steps + 1
    if steps > 200 {
      abort("poly_bezout_modp: not coprime modulo p")
    }
    // make the divisor monic
    let lc = r1[poly_deg(r1)]
    let ilc = @nf.inv_mod_p(lc, p)
    if ilc != 1 {
      r1 = poly_mod(poly_mul_mod(r1, [ilc], p), p)
      s1 = poly_mod(poly_mul_mod(s1, [ilc], p), p)
      t1 = poly_mod(poly_mul_mod(t1, [ilc], p), p)
    }
    let (q, r) = poly_divmod_mod(r0, r1, p)
    if poly_deg(r) == 0 && r[0] == 0 {
      break
    }
    r0 = r1
    r1 = r
    let ns = poly_mod(poly_sub(s0, poly_mul_mod(q, s1, p)), p)
    let nt = poly_mod(poly_sub(t0, poly_mul_mod(q, t1, p)), p)
    s0 = s1
    t0 = t1
    s1 = ns
    t1 = nt
  }
  // r1 is a non-zero constant; scale the cofactors so that s·g + t·h = 1
  let lc = r1[0]
  if lc == 0 {
    abort("poly_bezout_modp: gcd is zero")
  }
  let ilc = @nf.inv_mod_p(lc, p)
  (
    poly_mod(poly_mul_mod(s1, [ilc], p), p),
    poly_mod(poly_mul_mod(t1, [ilc], p), p),
  )
}

///|
/// T4 (Hensel factorisation).  Given f ≡ g₀·h₀ (mod p) with g₀, h₀ monic and
/// coprime mod p, compute the unique lifts g ≡ g₀, h ≡ h₀ (mod p) with
/// f ≡ g·h (mod p^prec).
pub fn hensel_factor(
  f : Array[Int32],
  g0 : Array[Int32],
  h0 : Array[Int32],
  p : Int32,
  prec : Int32,
) -> (Array[Int32], Array[Int32]) {
  let mut g = poly_mod(g0, p)
  let mut h = poly_mod(h0, p)
  let mut k = 1
  let mut steps = 0
  while k < prec && steps < 200 {
    steps = steps + 1
    let k2 = if 2 * k > prec { prec } else { 2 * k }
    let m = padic_prec(p, k2)
    let fm = poly_mod(f, m)
    let e = poly_mod(poly_sub(fm, poly_mul_mod(g, h, m)), m)
    if poly_deg(e) == 0 && e[0] == 0 {
      k = k2
      continue
    }
    let (_s, t) = bezout_lift(g, h, p, k)
    // dg = (e*t) mod g,  dh = (e - dg*h) / g   (exact, g monic)
    let (_, dg) = poly_divmod_mod(poly_mod(poly_mul_mod(e, t, m), m), g, m)
    let (dh, rr) = poly_divmod_mod(
      poly_mod(poly_sub(e, poly_mul_mod(dg, h, m)), m),
      g,
      m,
    )
    if poly_deg(rr) != 0 || rr[0] != 0 {
      abort("hensel_factor: exact division failed")
    }
    g = poly_mod(poly_add(g, dg), m)
    h = poly_mod(poly_add(h, dh), m)
    k = k2
  }
  let m = padic_prec(p, prec)
  (poly_mod(g, m), poly_mod(h, m))
}

// ---------------------------------------------------------------------------
// T5: Newton polygon.
// ---------------------------------------------------------------------------

///|
/// The lower convex hull of {(i, v_p(a_i)) : a_i ≠ 0}, returned as the list
/// of segments (i₁, v₁, i₂, v₂) from left to right.  Segments have strictly
/// increasing slopes, and the slope of (i₁,v₁)-(i₂,v₂) is (v₂−v₁)/(i₂−i₁):
/// the corresponding roots have valuation −slope = (v₁−v₂)/(i₂−i₁).
pub fn newton_polygon(
  cs : Array[Int32],
  p : Int32,
) -> Array[(Int32, Int32, Int32, Int32)] {
  let pts : Array[(Int32, Int32)] = []
  for i = 0; i < cs.length(); i = i + 1 {
    if cs[i] != 0 {
      pts.push((i, padic_val_z(cs[i], p)))
    }
  }
  // lower convex hull by the monotone chain
  let hull : Array[(Int32, Int32)] = []
  for k = 0; k < pts.length(); k = k + 1 {
    let (xi, vi) = pts[k]
    while hull.length() >= 2 {
      let (x1, v1) = hull[hull.length() - 2]
      let (x2, v2) = hull[hull.length() - 1]
      let cross = (x2 - x1) * (vi - v1) - (v2 - v1) * (xi - x1)
      if cross <= 0 {
        hull.pop() |> ignore
      } else {
        break
      }
    }
    hull.push((xi, vi))
  }
  let segs : Array[(Int32, Int32, Int32, Int32)] = []
  for i = 0; i + 1 < hull.length(); i = i + 1 {
    let (x1, v1) = hull[i]
    let (x2, v2) = hull[i + 1]
    segs.push((x1, v1, x2, v2))
  }
  segs
}

///|
/// T5: the multiset of root valuations read off the Newton polygon: a
/// segment (i₁,v₁,i₂,v₂) contributes i₂−i₁ roots of valuation
/// s = (v₁−v₂)/(i₂−i₁); returned as (numerator, denominator, multiplicity).
pub fn newton_root_valuations(
  cs : Array[Int32],
  p : Int32,
) -> Array[(Int32, Int32, Int32)] {
  let out : Array[(Int32, Int32, Int32)] = []
  for (i1, v1, i2, v2) in newton_polygon(cs, p) {
    let mult = i2 - i1
    let num = v1 - v2
    let den = i2 - i1
    let g = gcd_pos(if num < 0 { 0 - num } else { num }, den)
    out.push(
      (
        (if num < 0 { 0 - 1 } else { 1 }) *
        (if num < 0 { 0 - num } else { num }) /
        g,
        den / g,
        mult,
      ),
    )
  }
  out
}

///|
/// gcd(|a|,|b|) with the convention gcd(0,0) = 1 (so that reducing a
/// rational never divides by zero).  This is *not* `@tl.igcd`, which returns
/// 0 on (0,0).
pub fn gcd_pos(a : Int32, b : Int32) -> Int32 {
  let mut x = a
  let mut y = b
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  if x == 0 {
    1
  } else {
    x
  }
}

// ---------------------------------------------------------------------------
// T6: the valuation ring, its maximal ideal, and the residue field.
// ---------------------------------------------------------------------------

///|
/// Does x = num/den lie in the valuation ring O = {v ≥ 0} of Q_p?
pub fn in_valuation_ring(num : Int32, den : Int32, p : Int32) -> Bool {
  padic_val_q(num, den, p) >= 0
}

///|
/// Is x a unit of O, i.e. v(x) = 0?
pub fn is_valuation_unit(num : Int32, den : Int32, p : Int32) -> Bool {
  padic_val_q(num, den, p) == 0
}

///|
/// Is x in the maximal ideal m = {v > 0}?
pub fn in_maximal_ideal(num : Int32, den : Int32, p : Int32) -> Bool {
  padic_val_q(num, den, p) > 0
}

///|
/// The reduction map O → k(v) = F_p: for v(x) ≥ 0, x = num/den reduces to
/// (num mod p)·(den mod p)^{−1} in F_p.
pub fn residue(num : Int32, den : Int32, p : Int32) -> Int32 {
  if padic_val_q(num, den, p) < 0 {
    abort("residue: not in the valuation ring")
  }
  let vn = padic_val_z(num, p)
  let vd = padic_val_z(den, p)
  let c = if vn < vd { vn } else { vd }
  let nn = divide_exact(num, p, c)
  let dd = divide_exact(den, p, c)
  let inv = @nf.inv_mod_p(@nf.mod_pos(dd, p), p)
  @nf.mod_pos(@nf.mod_pos(nn, p) * inv, p)
}

///|
fn divide_exact(n : Int32, p : Int32, k : Int32) -> Int32 {
  let mut r = n
  let mut i = 0
  while i < k {
    r = r / p
    i = i + 1
  }
  r
}

///|
/// Addition in the residue field F_p.
pub fn residue_add(a : Int32, b : Int32, p : Int32) -> Int32 {
  @nf.mod_pos(a + b, p)
}

///|
pub fn residue_mul(a : Int32, b : Int32, p : Int32) -> Int32 {
  @nf.mod_pos(a * b, p)
}

///|
/// Application of T3: the p-adic square root.  For odd p and a a unit which
/// is a quadratic residue mod p, f(x) = x² − a has a simple root mod p
/// (f'(r) = 2r ≢ 0), so Hensel gives r̃ ∈ Z_p with r̃² = a to any precision.
pub fn padic_sqrt(a : Int32, p : Int32, prec : Int32) -> Int32 {
  let mut r = 0
  let mut x = 1
  while x < p {
    if @nf.mod_pos(x * x - a, p) == 0 {
      r = x
      break
    }
    x = x + 1
  }
  if r == 0 {
    abort("padic_sqrt: not a quadratic residue modulo p")
  }
  hensel_lift([0 - a, 0, 1], p, r, prec)
}

///|
/// Application of T3: the Teichmuller representative.  For x ∈ Z_p^× the
/// sequence x, x^p, x^{p²}, … converges to the unique (p−1)-st root of unity
/// ω(x) congruent to x mod p; then x = ω(x)·⟨x⟩ with ⟨x⟩ ∈ 1 + p Z_p.
pub fn teichmuller(x : Int32, p : Int32, prec : Int32) -> Int32 {
  let mut a = @nf.mod_pos(x, p)
  let mut steps = 0
  while steps < prec + 8 {
    steps = steps + 1
    let nxt = padic_pow(a, p, p, prec)
    if nxt == a {
      return a
    }
    a = nxt
  }
  a
}
