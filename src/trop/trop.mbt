/// 熱帶化 (TROPICALIZATION) — the min-plus (tropical) semiring, tropical
/// varieties, and Kapranov's theorem, machine-checked.
///
/// Definitions
/// -----------
/// The *tropical semiring* is T = R ∪ {∞} with
///
///     x ⊕ y := min(x, y)          (tropical addition)
///     x ⊙ y := x + y              (tropical multiplication)
///
/// additive identity ∞, multiplicative identity 0.  It is an idempotent
/// semiring (x ⊕ x = x) but not a ring: there are no additive inverses.
///
/// Let K be a field with a non-Archimedean valuation v (here K = Q, v = v_p).
/// The *tropicalisation* of a polynomial f = Σ_α c_α x^α ∈ K[x_1,…,x_n] is
///
///     trop(f)(w) = min_α ( v(c_α) + ⟨α, w⟩ ) ,
///
/// a piecewise-linear concave function R^n → T; the *tropical hypersurface*
/// (corner locus) V(trop f) is the set of w where the minimum is attained at
/// least twice.
///
/// Theorems implemented here
/// -------------------------
/// T1 (Semiring laws).  (T, ⊕, ⊙) is a commutative idempotent semiring with
/// the two neutral elements ∞ and 0; ⊙ distributes over ⊕.
/// T2 (Tropicalisation is a homomorphism).  For f, g ∈ K[x],
///         trop(f + g) ≥ trop(f) ⊕ trop(g)   (pointwise min),
///         trop(f · g) = trop(f) ⊙ trop(g)   (equality!),
/// so tropicalisation is a semiring homomorphism K[x] → T[x] modulo the
/// "cancellation" inequality for sums.
/// T3 (Kapranov / fundamental theorem, n = 1).  For f ∈ K[x] splitting as
/// f = c Π (x − r_i) over the algebraic closure, the tropical roots of
/// trop(f) — the w where the minimum is attained twice, with multiplicity the
/// "jump" — are exactly the valuations v(r_i).  Equivalently the tropical
/// roots are the negatives of the slopes of the Newton polygon of f.
/// T4 (Kapranov, n ≥ 1 via initial ideals).  w ∈ Trop(V(I)) iff the initial
/// ideal in_w(I) contains no monomial.  (Convention: our corner locus uses
/// min, the initial ideal uses max-weight terms, so the two are compared at
/// opposite signs: w ∈ Trop ⟺ −w is in the min-plus corner locus.)
/// T5 (Tropical matrices).  For A, B over K,
///         v((A B)_{ij}) ≥ min_k ( v(A_{ik}) + v(B_{kj}) ) ,
/// i.e. trop(A B) ≥ trop(A) ⊙ trop(B) entrywise, with equality iff no
/// cancellation occurs; the *tropical determinant*
///         tdet(A) = min_{σ ∈ S_n} Σ_i A_{i,σ(i)}
/// is the value of the classical assignment problem, and A is tropically
/// singular iff that minimum is attained at least twice.
/// T6 (Tropical Grassmannian Gr(2,4) = tree metrics).  A vector
/// (w_{ij}) ∈ R^6 lies in trop Gr(2,4) iff the tropical Plücker relation
///         min( w12 ⊙ w34 , w13 ⊙ w24 , w14 ⊙ w23 )
/// is attained at least twice.  Under w_{ij} = −d_{ij} this is exactly the
/// four-point condition characterising tree metrics on 4 leaves:
///         max( d12 + d34 , d13 + d24 , d14 + d23 )  is attained twice.

// ---------------------------------------------------------------------------
// The tropical semiring.
// ---------------------------------------------------------------------------

///|
/// The additive identity ∞ of the tropical semiring, represented by a large
/// sentinel (IEEE infinity is avoided so that the arithmetic stays exact).
pub fn trop_inf() -> Double {
  1.0e300
}

///|
pub fn trop_is_inf(a : Double) -> Bool {
  a > 5.0e299
}

///|
pub fn trop_add(a : Double, b : Double) -> Double {
  if a <= b {
    a
  } else {
    b
  }
}

///|
pub fn trop_mul(a : Double, b : Double) -> Double {
  if trop_is_inf(a) || trop_is_inf(b) {
    trop_inf()
  } else {
    a + b
  }
}

///|
pub fn trop_inv(a : Double) -> Double {
  if trop_is_inf(a) {
    trop_inf()
  } else {
    0.0 - a
  }
}

///|
pub fn trop_pow(a : Double, n : Int32) -> Double {
  if trop_is_inf(a) {
    trop_inf()
  } else {
    a * n.to_double()
  }
}

///|
/// The multiplicative identity of the tropical semiring.
pub fn trop_one() -> Double {
  0.0
}

///|
pub fn trop_zero() -> Double {
  trop_inf()
}

// ---------------------------------------------------------------------------
// Tropical polynomials in one variable: coefficient i = coefficient of x^i,
// trop_inf() marks an absent monomial.
// ---------------------------------------------------------------------------

///|
pub fn trop_eval(cs : Array[Double], x : Double) -> Double {
  let mut acc = trop_inf()
  for i = 0; i < cs.length(); i = i + 1 {
    let v = cs[i] + i.to_double() * x
    if trop_is_inf(cs[i]) {
      continue
    }
    if v < acc {
      acc = v
    }
  }
  acc
}

///|
/// The monomials at which the minimum is attained.
pub fn trop_argmins(cs : Array[Double], x : Double) -> Array[Int32] {
  let m = trop_eval(cs, x)
  let out : Array[Int32] = []
  for i = 0; i < cs.length(); i = i + 1 {
    if !trop_is_inf(cs[i]) && (cs[i] + i.to_double() * x - m).abs() < 1.0e-9 {
      out.push(i)
    }
  }
  out
}

///|
/// Is w a tropical root, i.e. does the minimum get attained at least twice?
pub fn trop_is_root(cs : Array[Double], x : Double) -> Bool {
  trop_argmins(cs, x).length() >= 2
}

///|
/// T3: the tropical roots, found by the pairwise crossing method (independent
/// of the Newton polygon): monomials i < j cross at
/// w = (c_j − c_i)/(i − j), and w is a root iff the minimum at w is attained
/// at least twice.  The multiplicity of w is (max index attaining − min index
/// attaining), i.e. the horizontal length of the corresponding segment.
pub fn trop_roots(cs : Array[Double]) -> Array[(Double, Int32)] {
  let cands : Array[Double] = []
  for i = 0; i < cs.length(); i = i + 1 {
    if trop_is_inf(cs[i]) {
      continue
    }
    for j = i + 1; j < cs.length(); j = j + 1 {
      if trop_is_inf(cs[j]) {
        continue
      }
      let w = (cs[j] - cs[i]) / (i - j).to_double()
      cands.push(w)
    }
  }
  // keep each root once, with its multiplicity
  let roots : Array[(Double, Int32)] = []
  for w in cands {
    if !trop_is_root(cs, w) {
      continue
    }
    let am = trop_argmins(cs, w)
    let mut lo = am[0]
    let mut hi = am[0]
    for k in am {
      if k < lo {
        lo = k
      }
      if k > hi {
        hi = k
      }
    }
    let mut seen = false
    for k = 0; k < roots.length(); k = k + 1 {
      let (rw, _m) = roots[k]
      if (rw - w).abs() < 1.0e-9 {
        seen = true
        break
      }
    }
    if !seen {
      roots.push((w, hi - lo))
    }
  }
  roots.sort_by(fn(a, b) { Double::compare(a.0, b.0) })
  roots
}

///|
pub fn trop_poly_add(a : Array[Double], b : Array[Double]) -> Array[Double] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[Double] = []
  for i = 0; i < n; i = i + 1 {
    let x = if i < a.length() { a[i] } else { trop_inf() }
    let y = if i < b.length() { b[i] } else { trop_inf() }
    out.push(trop_add(x, y))
  }
  out
}

///|
/// T2: min-plus convolution — the tropical product of polynomials.
pub fn trop_poly_mul(a : Array[Double], b : Array[Double]) -> Array[Double] {
  let out : Array[Double] = Array::make(a.length() + b.length() - 1, trop_inf())
  for i = 0; i < a.length(); i = i + 1 {
    if trop_is_inf(a[i]) {
      continue
    }
    for j = 0; j < b.length(); j = j + 1 {
      if trop_is_inf(b[j]) {
        continue
      }
      out[i + j] = trop_add(out[i + j], trop_mul(a[i], b[j]))
    }
  }
  out
}

///|
pub fn trop_poly_pow(cs : Array[Double], n : Int32) -> Array[Double] {
  let mut acc : Array[Double] = [trop_one()]
  let mut i = 0
  while i < n {
    acc = trop_poly_mul(acc, cs)
    i = i + 1
  }
  acc
}

///|
/// Tropicalisation of an integer polynomial with respect to v_p: the
/// coefficient of x^i becomes v_p(a_i), and ∞ for a vanishing coefficient.
pub fn tropicalize(cs : Array[Int32], p : Int32) -> Array[Double] {
  let out : Array[Double] = []
  for i = 0; i < cs.length(); i = i + 1 {
    if cs[i] == 0 {
      out.push(trop_inf())
    } else {
      out.push(@valued.padic_val_z(cs[i], p).to_double())
    }
  }
  out
}

// ---------------------------------------------------------------------------
// T4: multivariate tropical polynomials and the corner locus.
// ---------------------------------------------------------------------------

///|
pub(all) struct TT {
  c : Double
  e : Array[Int32]
}

///|
/// A multivariate tropical polynomial: a list of (coefficient, exponent).
pub type TPoly = Array[TT]

///|
pub fn tp_eval(f : TPoly, w : Array[Double]) -> Double {
  let mut acc = trop_inf()
  for t in f {
    let mut s = t.c
    let mut i = 0
    while i < t.e.length() && i < w.length() {
      s = s + t.e[i].to_double() * w[i]
      i = i + 1
    }
    if s < acc {
      acc = s
    }
  }
  acc
}

///|
pub fn tp_argmins(f : TPoly, w : Array[Double]) -> Int32 {
  let m = tp_eval(f, w)
  let mut c = 0
  for t in f {
    let mut s = t.c
    let mut i = 0
    while i < t.e.length() && i < w.length() {
      s = s + t.e[i].to_double() * w[i]
      i = i + 1
    }
    if (s - m).abs() < 1.0e-9 {
      c = c + 1
    }
  }
  c
}

///|
/// T4 (min convention): w is in the corner locus of f iff the minimum is
/// attained at least twice.
pub fn tp_in_corner_locus(f : TPoly, w : Array[Double]) -> Bool {
  tp_argmins(f, w) >= 2
}

///|
/// Read a classical integer polynomial (list of (coefficient, exponent)) as a
/// tropical polynomial via v_p.
pub fn tp_of(cs : Array[(Int32, Array[Int32])], p : Int32) -> TPoly {
  let out : TPoly = []
  for (c, e) in cs {
    out.push({ c: @valued.padic_val_z(c, p).to_double(), e, })
  }
  out
}

// ---------------------------------------------------------------------------
// T5: tropical matrices.
// ---------------------------------------------------------------------------

///|
/// All permutations of 0..n−1 (n ≤ 7).
pub fn permutations(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  let used : Array[Bool] = Array::make(n, false)
  gen_perms(n, cur, used, out)
  out
}

///|
fn gen_perms(
  n : Int32,
  cur : Array[Int32],
  used : Array[Bool],
  out : Array[Array[Int32]],
) -> Unit {
  if cur.length() == n {
    out.push(cur.copy())
    return
  }
  let mut i = 0
  while i < n {
    if !used[i] {
      used[i] = true
      cur.push(i)
      gen_perms(n, cur, used, out)
      cur.pop() |> ignore
      used[i] = false
    }
    i = i + 1
  }
}

///|
/// The (min, +) product of matrices over the tropical semiring.
pub fn trop_mat_mul(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let m = b[0].length()
  let out : Array[Array[Double]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Double] = []
    for j = 0; j < m; j = j + 1 {
      let mut acc = trop_inf()
      for k = 0; k < b.length(); k = k + 1 {
        acc = trop_add(acc, trop_mul(a[i][k], b[k][j]))
      }
      row.push(acc)
    }
    out.push(row)
  }
  out
}

///|
/// T5: the tropical determinant min_{σ} Σ_i a_{i,σ(i)} together with the
/// number of permutations realising it (A is tropically singular iff ≥ 2).
pub fn trop_det(a : Array[Array[Double]]) -> (Double, Int32) {
  let n = a.length()
  let ps = permutations(n)
  let mut best = trop_inf()
  let mut count = 0
  for s in ps {
    let mut acc = trop_one()
    for i = 0; i < n; i = i + 1 {
      acc = trop_mul(acc, a[i][s[i]])
    }
    if acc < best - 1.0e-12 {
      best = acc
      count = 1
    } else if (acc - best).abs() < 1.0e-12 {
      count = count + 1
    }
  }
  (best, count)
}

///|
pub fn trop_singular(a : Array[Array[Double]]) -> Bool {
  let (_d, c) = trop_det(a)
  c >= 2
}

///|
/// Entrywise valuation of an integer matrix.
pub fn val_matrix(a : Array[Array[Int32]], p : Int32) -> Array[Array[Double]] {
  let out : Array[Array[Double]] = []
  for row in a {
    let r : Array[Double] = []
    for x in row {
      if x == 0 {
        r.push(trop_inf())
      } else {
        r.push(@valued.padic_val_z(x, p).to_double())
      }
    }
    out.push(r)
  }
  out
}

///|
/// Ordinary integer matrix product, used to test the valuation inequality
/// v((AB)_ij) >= min_k (v(A_ik) + v(B_kj)).  Delegates to `@nf.mat_mul`,
/// which is the single implementation.
pub fn mat_mul_int(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]]
) -> Array[Array[Int32]] {
  @nf.mat_mul(a, b)
}

// ---------------------------------------------------------------------------
// T6: the tropical Grassmannian Gr(2,4) and the four-point condition.
// ---------------------------------------------------------------------------

///|
/// The three terms of the tropical Plücker relation for Gr(2,4), in the order
/// w12⊙w34, w13⊙w24, w14⊙w23 (indices as in the input vector
/// [w12, w13, w14, w23, w24, w34]).
pub fn pluecker_terms(w : Array[Double]) -> Array[Double] {
  [trop_mul(w[0], w[5]), trop_mul(w[1], w[4]), trop_mul(w[2], w[3])]
}

///|
/// T6: (w_ij) ∈ trop Gr(2,4) iff the minimum of the three Plücker terms is
/// attained at least twice.
pub fn in_trop_grassmannian(w : Array[Double]) -> Bool {
  let t = pluecker_terms(w)
  let m = trop_add(trop_add(t[0], t[1]), t[2])
  let mut c = 0
  for i = 0; i < 3; i = i + 1 {
    if (t[i] - m).abs() < 1.0e-9 {
      c = c + 1
    }
  }
  c >= 2
}

///|
/// The tree metric of the quartet tree ((0,1),(2,3)) with pendant edge
/// lengths a0..a3 and internal edge e, as the vector
/// [d01, d02, d03, d12, d13, d23].
pub fn quartet_metric(
  a0 : Double,
  a1 : Double,
  a2 : Double,
  a3 : Double,
  e : Double,
) -> Array[Double] {
  [a0 + a1, a0 + e + a2, a0 + e + a3, a1 + e + a2, a1 + e + a3, a2 + a3]
}

///|
/// Convert a metric [d01, d02, d03, d12, d13, d23] to the Plücker-indexed
/// vector [w12, w13, w14, w23, w24, w34] with w = −d (leaves 1..4 = 0..3).
pub fn metric_to_pluecker(d : Array[Double]) -> Array[Double] {
  [0.0 - d[0], 0.0 - d[1], 0.0 - d[2], 0.0 - d[3], 0.0 - d[4], 0.0 - d[5]]
}

///|
/// The three sums of the four-point condition (max convention), in the order
/// d12+d34, d13+d24, d14+d23 — a tree metric attains the maximum twice.
pub fn four_point_sums(d : Array[Double]) -> Array[Double] {
  [d[0] + d[5], d[1] + d[4], d[2] + d[3]]
}

///|
/// Four-point condition: max(d12+d34, d13+d24, d14+d23) attained twice.
pub fn is_tree_metric(d : Array[Double]) -> Bool {
  let s = four_point_sums(d)
  let m = if s[0] > s[1] { s[0] } else { s[1] }
  let m = if m > s[2] { m } else { s[2] }
  let mut c = 0
  for i = 0; i < 3; i = i + 1 {
    if (s[i] - m).abs() < 1.0e-9 {
      c = c + 1
    }
  }
  c >= 2
}

///|
/// T4 (synthesis, Kapranov's theorem).  For a principal ideal I = ⟨f⟩,
///         w ∈ Trop(V(I))  ⟺  in_w(I) contains no monomial
///                         ⟺  the minimum of trop(f)(−w) is attained twice
/// (the sign flip is the passage between the max-convention used by initial
/// forms and the min-convention of the tropical semiring).  For a
/// non-principal ideal the corner-locus condition on each generator is only
/// *necessary*, so both sides are compared explicitly here.
pub fn kapranov_agree(
  g : Array[@nf.Poly],
  f : TPoly,
  w : Array[Int32],
  p : Int32,
  cmp : @nf.Cmp,
) -> Bool {
  let initial = @nf.is_tropical(g, w, p, cmp)
  let neg : Array[Double] = []
  for x in w {
    neg.push(0.0 - x.to_double())
  }
  initial == tp_in_corner_locus(f, neg)
}

///|
/// The necessary form of the corner-locus condition for a family of
/// generators: every generator must attain its minimum at least twice at w.
pub fn all_generators_tropical(fs : Array[TPoly], w : Array[Double]) -> Bool {
  for f in fs {
    if !tp_in_corner_locus(f, w) {
      return false
    }
  }
  true
}
