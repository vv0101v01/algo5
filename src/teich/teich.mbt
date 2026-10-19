// Copyright 2026. Apache-2.0.
//
// The Teichmüller space of the once-punctured torus.
//
// ---------------------------------------------------------------------------
// The mathematics
// ---------------------------------------------------------------------------
// Let S be a once-punctured torus and let A, B ∈ SL(2,R) be the images of a
// basis of π₁(S) under a Fuchsian representation ρ with parabolic commutator
// (the puncture).  Put
//
//     x = tr A,   y = tr B,   z = tr AB.
//
// Theorem (Fricke).  tr[A,B] = x² + y² + z² − x y z − 2, and the Teichmüller
// space is the *Markoff cubic*
//
//     T(S)  ≅  { (x,y,z) ∈ R³_{>2} : x² + y² + z² = x y z }.
//
// (Parabolicity of the commutator is tr[A,B] = −2, which is exactly the
// cubic.)  "同構即相同": a point of Teichmüller space *is* the triple of
// traces — no quotient, no choice of marking beyond the basis (A,B).
//
// Theorem (Fricke–Vogt).  The mapping class group acts on the cubic by the
// Vieta involutions (x,y,z) ↦ (yz−x, y, z) and permutations; the integer
// points are the (3× classical) Markoff numbers.
//
// Theorem (McShane).  For every hyperbolic once-punctured torus
//
//     Σ_γ  1 / (1 + e^{ℓ(γ)})  =  1/2,
//
// the sum being over all simple closed geodesics γ.  With x = 2 cosh(ℓ/2),
//
//     1/(1+e^ℓ) = (1 − √(1 − 4/x²)) / 2.
//
// `mcshane_partial` computes the partial sums over all simple closed curves of
// slope p/q with |p|, |q| ≤ N (simple closed curves ↔ primitive classes
// (p,q) ∈ Z² up to sign), and the test verifies convergence to 1/2.
//
// Theorem (Fenchel–Nielsen).  Cutting S along the geodesic A and regluing with
// twist t ∈ R gives the flow (A, B) ↦ (A, A^{t/2} B A^{t/2}) on the character
// variety.  It preserves: tr A (the length coordinate), the cusp condition
// tr[A,B] = −2, the Markoff cubic, and the McShane identity; and it satisfies
// the flow law.  All four are checked numerically.

// ---------------------------------------------------------------------------
// 2×2 real matrices
// ---------------------------------------------------------------------------

///|
/// A 2×2 matrix as [[a,b],[c,d]].
pub type Mat2 = Array[Array[Double]]

///|
pub fn m2(a : Double, b : Double, c : Double, d : Double) -> Mat2 {
  [[a, b], [c, d]]
}

///|
pub fn m2_mul(x : Mat2, y : Mat2) -> Mat2 {
  [
    [
      x[0][0] * y[0][0] + x[0][1] * y[1][0],
      x[0][0] * y[0][1] + x[0][1] * y[1][1],
    ],
    [
      x[1][0] * y[0][0] + x[1][1] * y[1][0],
      x[1][0] * y[0][1] + x[1][1] * y[1][1],
    ],
  ]
}

///|
pub fn m2_inv(x : Mat2) -> Mat2 {
  let det = m2_det(x)
  if det == 0.0 {
    abort("m2_inv: singular")
  }
  [[x[1][1] / det, 0.0 - x[0][1] / det], [0.0 - x[1][0] / det, x[0][0] / det]]
}

///|
pub fn m2_det(x : Mat2) -> Double {
  x[0][0] * x[1][1] - x[0][1] * x[1][0]
}

///|
pub fn m2_tr(x : Mat2) -> Double {
  x[0][0] + x[1][1]
}

///|
/// Integer power.
pub fn m2_pow(x : Mat2, n : Int32) -> Mat2 {
  if n < 0 {
    return m2_pow(m2_inv(x), 0 - n)
  }
  let mut r : Mat2 = [[1.0, 0.0], [0.0, 1.0]]
  let mut i = 0
  while i < n {
    r = m2_mul(r, x)
    i = i + 1
  }
  r
}

///|
/// Real power of a hyperbolic matrix: if A has eigenvalues λ^{±1} with
/// λ > 1, then A^t = P diag(λ^t, λ^{−t}) P^{−1}.  Used by the Fenchel–
/// Nielsen twist flow.
pub fn m2_pow_real(a : Mat2, t : Double) -> Mat2 {
  let tr = m2_tr(a)
  // eigenvalues of a unimodular 2x2 matrix: (tr ± sqrt(tr^2-4))/2
  let disc = tr * tr - 4.0
  if disc <= 0.0 {
    abort("m2_pow_real: not hyperbolic")
  }
  let rt = disc.sqrt()
  let lam = (tr + rt) / 2.0
  let mu = (tr - rt) / 2.0
  // A = lam*P_+ + mu*P_- with P_± the spectral projections; for 2x2:
  //   A^t = (lam^t (A - mu I) - mu^t (A - lam I)) / (lam - mu)
  let lt = @math.exp(@math.ln(lam.abs()) * t)
  let mt = @math.exp(@math.ln(mu.abs()) * t)
  let i0 = a[0][0] - mu
  let i1 = a[1][1] - mu
  let j0 = a[0][0] - lam
  let j1 = a[1][1] - lam
  [
    [(lt * i0 - mt * j0) / (lam - mu), a[0][1] * (lt - mt) / (lam - mu)],
    [a[1][0] * (lt - mt) / (lam - mu), (lt * i1 - mt * j1) / (lam - mu)],
  ]
}

///|
/// The commutator [A,B] = A B A^{-1} B^{-1}.
pub fn commutator(a : Mat2, b : Mat2) -> Mat2 {
  m2_mul(m2_mul(m2_mul(a, b), m2_inv(a)), m2_inv(b))
}

///|
/// Fricke's identity: tr[A,B] = x²+y²+z² − xyz − 2.
pub fn fricke_commutator_trace(x : Double, y : Double, z : Double) -> Double {
  x * x + y * y + z * z - x * y * z - 2.0
}

///|
/// The Markoff cubic evaluated at (x,y,z): zero iff the commutator is
/// parabolic (tr = −2) — i.e. iff the traces lie in T(S).
pub fn markoff_defect(x : Double, y : Double, z : Double) -> Double {
  x * x + y * y + z * z - x * y * z
}

///|
/// The standard representation of the *modular* once-punctured torus:
/// x = y = z = 3, the most symmetric point of T(S).
pub fn modular_torus() -> (Mat2, Mat2) {
  ([[1.0, 1.0], [1.0, 2.0]], [[1.0, 0.0 - 1.0], [0.0 - 1.0, 2.0]])
}

///|
/// Length of the closed geodesic with trace `x`: 2 cosh(ℓ/2) = |x|.
pub fn length_from_trace(x : Double) -> Double {
  2.0 * @math.acosh(x.abs() / 2.0)
}

///|
/// McShane summand: 1/(1+e^ℓ) = (1 − √(1 − 4/x²))/2.
pub fn mcshane_term(x : Double) -> Double {
  let t = 1.0 - 4.0 / (x * x)
  if t < 0.0 {
    0.0
  } else {
    (1.0 - t.sqrt()) / 2.0
  }
}

// ---------------------------------------------------------------------------
// Markoff triples
// ---------------------------------------------------------------------------

///|
/// Vieta involution on the first coordinate: x ↦ yz − x.
pub fn vieta_x(x : Double, y : Double, z : Double) -> Double {
  y * z - x
}

///|
/// Generate Markoff triples by breadth-first Vieta moves, up to a bound on
/// the largest coordinate.  Each triple (x,y,z) satisfies the cubic.
pub fn markoff_triples(
  x0 : Double,
  y0 : Double,
  z0 : Double,
  bound : Double,
) -> Array[(Double, Double, Double)] {
  let out : Array[(Double, Double, Double)] = Array::make(0, (0.0, 0.0, 0.0))
  let mut frontier : Array[(Double, Double, Double)] = Array::make(
    0,
    (0.0, 0.0, 0.0),
  )
  frontier.push((x0, y0, z0))
  out.push((x0, y0, z0))
  let mut rounds = 0
  while frontier.length() > 0 && rounds < 40 {
    rounds = rounds + 1
    let next : Array[(Double, Double, Double)] = Array::make(0, (0.0, 0.0, 0.0))
    for t in frontier {
      let (x, y, z) = t
      let cands = [
        (vieta_x(x, y, z), y, z),
        (x, vieta_x(y, x, z), z),
        (x, y, vieta_x(z, x, y)),
      ]
      for c in cands {
        let (a, b, c2) = c
        if a <= 2.0 || b <= 2.0 || c2 <= 2.0 {
          continue
        }
        if a > bound || b > bound || c2 > bound {
          continue
        }
        // avoid going back to the parent and duplicates
        let mut seen = false
        for o in out {
          let (p, q, r) = o
          if (p - a).abs() < 1.0e-9 &&
            (q - b).abs() < 1.0e-9 &&
            (r - c2).abs() < 1.0e-9 {
            seen = true
          }
        }
        if !seen {
          out.push(c)
          next.push(c)
        }
      }
    }
    frontier = next
  }
  out
}

// ---------------------------------------------------------------------------
// simple closed curves of the once-punctured torus
// ---------------------------------------------------------------------------
// Simple closed curves ↔ primitive classes (p,q) ∈ Z² (up to sign).  We build
// a word in π₁ = ⟨A,B⟩ representing the curve by lifting the Euclidean
// algorithm to Aut(F₂), where the two Dehn twists act by
//     α : (A,B) ↦ (A, BA)   on homology (a,b) ↦ (a+b, b)
//     β : (A,B) ↦ (AB, B)   on homology (a,b) ↦ (a, a+b)
// and their inverses.  The word is then evaluated in SL(2,R).

///|
/// Word tokens.
pub type Tok = Int32

///|
pub fn tok_a() -> Tok {
  0
}

///|
pub fn tok_ai() -> Tok {
  1
}

///|
pub fn tok_b() -> Tok {
  2
}



///|
fn concat_words(x : Array[Tok], y : Array[Tok]) -> Array[Tok] {
  let out : Array[Tok] = Array::make(0, 0)
  for t in x {
    out.push(t)
  }
  for t in y {
    out.push(t)
  }
  out
}


///|
/// Abelianisation of a word: (#A, #B) with signs.
pub fn abelianisation(w : Array[Tok]) -> (Int32, Int32) {
  let mut a = 0
  let mut b = 0
  for t in w {
    match t {
      0 => a = a + 1
      1 => a = a - 1
      2 => b = b + 1
      _ => b = b - 1
    }
  }
  (a, b)
}

///| Bridge to the certified free-group machinery of `src/path`

///| (路徑空間).  A word in the once-punctured torus group

///| π₁(S) = ⟨A, B⟩ ≅ F₂ is an element of the *free groupoid* on one vertex,

///| so equality of curves-up-to-homotopy is exactly equality of free

///| reductions — the "同構即相同" statement for π₁.  Tokens are re-encoded as

///| free-group letters (letter a has inverse −(a+1)):

///|
///        A ↦ 0 , A⁻¹ ↦ −1 , B ↦ 1 , B⁻¹ ↦ −2 .
pub fn letters_of(w : Array[Tok]) -> Array[Int32] {
  let out : Array[Int32] = Array::make(0, 0)
  for t in w {
    out.push(
      if t == 0 {
        0
      } else if t == 1 {
        0 - 1
      } else if t == 2 {
        1
      } else {
        0 - 2
      },
    )
  }
  out
}

///|
/// Is the word freely reduced (no adjacent x x⁻¹)?
pub fn word_reduced(w : Array[Tok]) -> Bool {
  let ls = letters_of(w)
  @path.reduce(ls) == ls
}


///|
/// The word of the simple closed curve of primitive class (p,q).
///
/// Construction (Stern–Brocot / Farey recursion).  Simple closed curves on
/// the punctured torus correspond bijectively to primitive classes
/// (p,q) ∈ Z² up to sign.  If α, β are curves meeting exactly once — i.e.
/// their classes are *Farey neighbours*, a/b and c/d with bc − ad = 1 — then
/// the concatenated word αβ represents the curve of class (a+c)/(b+d).
/// Starting from the neighbours 0/1 (word B) and 1/0 (word A) (or their
/// mirror (−1)/0 (word A^{-1}) and 0/1 for negative slopes) the Stern–Brocot
/// descent therefore reaches p/q in O(log) steps.  Correctness is verified
/// in the tests by checking that the abelianisation of the result is ±(p,q).
pub fn curve_word(p : Int32, q : Int32) -> Array[Tok] {
  if q == 0 {
    return if p > 0 { [tok_a()] } else { [tok_ai()] }
  }
  let pp = if q < 0 { 0 - p } else { p }
  let qq = if q < 0 { 0 - q } else { q }
  if pp == 0 && qq == 1 {
    return [tok_b()]
  }
  let mut al = 0
  let mut bl = 1
  let mut wl : Array[Tok] = [tok_b()]
  let mut ah = 1
  let mut bh = 0
  let mut wh : Array[Tok] = [tok_a()]
  if pp < 0 {
    al = 0 - 1
    bl = 0
    wl = [tok_ai()]
    ah = 0
    bh = 1
    wh = [tok_b()]
  }
  let mut steps = 0
  while steps < 100000 {
    steps = steps + 1
    let am = al + ah
    let bm = bl + bh
    if pp * bm == am * qq {
      return concat_words(wl, wh)
    }
    if pp * bm < am * qq {
      ah = am
      bh = bm
      wh = concat_words(wl, wh)
    } else {
      al = am
      bl = bm
      wl = concat_words(wl, wh)
    }
  }
  abort("curve_word: descent did not terminate")
}

///|
/// Evaluate a word in SL(2,R).
pub fn eval_word(a : Mat2, b : Mat2, w : Array[Tok]) -> Mat2 {
  let mut r : Mat2 = [[1.0, 0.0], [0.0, 1.0]]
  for t in w {
    r = m2_mul(r, mat_of_tok(a, b, t))
  }
  r
}

///|
fn mat_of_tok(a : Mat2, b : Mat2, t : Tok) -> Mat2 {
  match t {
    0 => a
    1 => m2_inv(a)
    2 => b
    _ => m2_inv(b)
  }
}

///|
/// Trace of the simple closed curve of class (p,q) in the representation
/// (A,B).
pub fn curve_trace(a : Mat2, b : Mat2, p : Int32, q : Int32) -> Double {
  m2_tr(eval_word(a, b, curve_word(p, q)))
}

///|
/// All primitive classes (p,q) up to sign with max(|p|,|q|) ≤ N.
/// Normalised so that the first non-zero coordinate is positive.
pub fn primitive_classes(n : Int32) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = Array::make(0, (0, 0))
  let mut p = 0 - n
  while p <= n {
    let mut q = 0 - n
    while q <= n {
      if !(p == 0 && q == 0) && gcd_i(p, q) == 1 {
        // normalise the sign
        if p > 0 || (p == 0 && q > 0) {
          out.push((p, q))
        }
      }
      q = q + 1
    }
    p = p + 1
  }
  out
}

///|
/// gcd(|a|,|b|).  Delegates to `@tl.igcd`: one implementation, shared.
pub fn gcd_i(a : Int32, b : Int32) -> Int32 {
  @tl.igcd(a, b)
}

///|
/// Partial McShane sum: Σ over simple closed curves of slope (p,q) with
/// max(|p|,|q|) ≤ N of 1/(1+e^{ℓ}).
pub fn mcshane_partial(a : Mat2, b : Mat2, n : Int32) -> Double {
  let mut s = 0.0
  for (p, q) in primitive_classes(n) {
    let x = curve_trace(a, b, p, q)
    s = s + mcshane_term(x)
  }
  s
}

///|
/// The length spectrum (sorted traces) of the simple closed geodesics of
/// slope (p,q), max(|p|,|q|) ≤ N.
pub fn length_spectrum(
  a : Mat2,
  b : Mat2,
  n : Int32,
) -> Array[(Int32, Int32, Double)] {
  let out : Array[(Int32, Int32, Double)] = Array::make(0, (0, 0, 0.0))
  for (p, q) in primitive_classes(n) {
    let x = curve_trace(a, b, p, q)
    out.push((p, q, length_from_trace(x)))
  }
  out
}

// ---------------------------------------------------------------------------
// Fenchel–Nielsen twist flow
// ---------------------------------------------------------------------------

///|
/// The twist flow along the geodesic A:
///     (A, B) ↦ (A, A^{t/2} · B · A^{t/2}),   t ∈ R.
/// Two exact consequences (both verified in the tests):
///   * tr[A, B] is **constant** along the flow, because
///       tr[A, A^s B A^s] = tr[A^{s+1} B A^{-1} B^{-1} A^{-s}]
///                        = tr[A B A^{-1} B^{-1}]  (cyclicity of tr),
///     so the commutator stays parabolic and the flow stays inside T(S);
///   * the flow law holds exactly: twist(t₁) ∘ twist(t₂) = twist(t₁+t₂),
///     since powers of A commute.
/// t = 1 is the right Dehn twist about A (same character: tr B' = tr AB and
/// tr A B' = tr A²B).
pub fn fn_twist(a : Mat2, b : Mat2, t : Double) -> (Mat2, Mat2) {
  let h = m2_pow_real(a, t / 2.0)
  (a, m2_mul(m2_mul(h, b), h))
}

///|
/// Fenchel–Nielsen coordinates (ℓ, τ) of a point of T(S) with respect to
/// the curve A.
///
/// Derivation.  Conjugate into the eigenbasis of A (eigenvalues λ^{±1} with
/// λ = e^{ℓ/2}) and write the twisted matrix as
///     B(s) = A^s B A^s = [[a·e^{sℓ}, b], [c, d·e^{-sℓ}]],   s = τ/2.
/// With A₀ = a e^{sℓ} and D₀ = d e^{-sℓ}:
///     y = tr B(s)   = A₀ + D₀,
///     z = tr A·B(s) = λ A₀ + λ^{-1} D₀.
/// The product A₀D₀ = a d is **invariant** along the flow, and min_s y =
/// 2√(A₀D₀).  Hence the twist, measured from the symmetric (untwisted) point
/// of the orbit and normalised so that the Dehn twist shifts it by 1, is
///     τ = (2/ℓ) · arccosh( y / (2√(A₀D₀)) ) · sign(A₀ − D₀).
pub fn fn_coordinates(a : Mat2, b : Mat2) -> (Double, Double) {
  let x = m2_tr(a)
  let y = m2_tr(b)
  let z = m2_tr(m2_mul(a, b))
  (length_from_trace(x), twist_from_traces(x, y, z))
}

///|
/// The twist coordinate from the trace triple; see `fn_coordinates`.
pub fn twist_from_traces(x : Double, y : Double, z : Double) -> Double {
  let ell = length_from_trace(x)
  let lam = @math.exp(ell / 2.0)
  let denom = lam - 1.0 / lam
  let a0 = (z - y / lam) / denom
  let d0 = (lam * y - z) / denom
  let prod = a0 * d0
  if prod <= 0.0 || ell <= 0.0 {
    return 0.0
  }
  let ymin = 2.0 * prod.sqrt()
  let ratio = y / ymin
  let t = @math.acosh(if ratio < 1.0 { 1.0 } else { ratio })
  let sgn = if a0 - d0 >= 0.0 { 1.0 } else { 0.0 - 1.0 }
  2.0 * sgn * t / ell
}

///|
/// The invariant product A₀D₀ of the twist orbit — constant along the flow.
pub fn twist_orbit_invariant(x : Double, y : Double, z : Double) -> Double {
  let ell = length_from_trace(x)
  let lam = @math.exp(ell / 2.0)
  let denom = lam - 1.0 / lam
  let a0 = (z - y / lam) / denom
  let d0 = (lam * y - z) / denom
  a0 * d0
}
