/// 範疇化 (CATEGORIFICATION) — replacing sets by categories, functions by
/// functors, and equations by natural isomorphisms; the decategorification
/// recovers the original structure.  Machine-checked on finite objects.
///
/// The slogan: a *categorification* of a set S with structure is a category C
/// together with a "decategorification" map K₀(C) → S that is a homomorphism
/// of the corresponding algebraic structures, under which isomorphism in C
/// becomes equality in S — 同構即相同.
///
/// Theorems implemented here
/// -------------------------
/// T1 (N is categorified by FinSet).  In the category FinSet of finite sets,
///     A ≅ B  ⟺  |A| = |B|                       (同構即相同),
///     |A ⊔ B| = |A| + |B|,   |A × B| = |A|·|B|,   |B^A| = |B|^{|A|},
///     |Aut(A)| = |A|!,
/// and FinSet is cartesian closed: the standard bijections
///     C^{A⊔B} ≅ C^A × C^B,   (A × B)^C ≅ A^C × B^C,   (C^B)^A ≅ C^{B×A}
/// are *explicitly constructed* and verified to be bijections.  The binomial
/// theorem is categorified by the bijection
///     (A ⊔ B)^{[n]} ≅ ⊔_{k=0}^{n} C(n,k) × A^{[k]} × B^{[n−k]},
/// also constructed explicitly; decategorifying gives (a+b)^n = Σ C(n,k)a^k b^{n−k}.
/// T2 (Gaussian binomials are categorified by graded vector spaces).  Let
/// V_d be the graded vector space over F_p with one basis element in each
/// degree 0, 1, …, d−1.  Then
///     Λ^n(V_d) has Hilbert series  q^{n(n−1)/2} · [d choose n]_q ,
///     S^n(V_d) has Hilbert series  [d+n−1 choose n]_q ,
/// and two finite-dimensional graded vector spaces are isomorphic *as graded
/// vector spaces* iff their Hilbert series are equal (同構即相同), an
/// isomorphism being constructed degree by degree.  K₀(grVect) ≅ Z[q,q^{−1}]
/// with [V ⊗ W] = [V]·[W] and [V ⊕ W] = [V] + [W].
/// T3 (K₀ and Euler characteristic).  Decategorifying the derived category
/// of `src/derived` gives K₀(D^b(Z)) ≅ Z via the Euler characteristic, and
/// the class of a complex can be computed either from the chain groups or
/// from the homology:  [C] = Σ(−1)^n [C_n] = Σ(−1)^n [H_n(C)].

// ---------------------------------------------------------------------------
// T1: FinSet as a categorification of N.
// ---------------------------------------------------------------------------

///|
/// A finite set is presented by its (distinct) elements.
pub type FinSet = Array[Int32]

///|
/// A function is presented by the list of the images of the elements.
pub type Fn = Array[Int32]

///|
/// Integer power a^n for n >= 0; shared with `@tl` so the algorithm has a
/// single implementation.
pub fn ipow(a : Int32, n : Int32) -> Int32 {
  @tl.ipow(a, n)
}

///|
pub fn factorial(n : Int32) -> Int32 {
  let mut r = 1
  let mut i = 2
  while i <= n {
    r = r * i
    i = i + 1
  }
  r
}

///|
pub fn binomial(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    0
  } else {
    factorial(n) / (factorial(k) * factorial(n - k))
  }
}

///|
/// The function with the given mixed-radix code: f(a[i]) = b[code_i].
pub fn fun_of(a : FinSet, b : FinSet, code : Int32) -> Fn {
  let nb = b.length()
  let mut c = code
  let out : Fn = []
  for i = 0; i < a.length(); i = i + 1 {
    out.push(b[c % nb])
    c = c / nb
  }
  out
}

///|
/// All functions A → B, enumerated.
pub fn all_functions(a : FinSet, b : FinSet) -> Array[Fn] {
  let total = ipow(b.length(), a.length())
  let out : Array[Fn] = []
  for c = 0; c < total; c = c + 1 {
    out.push(fun_of(a, b, c))
  }
  out
}

///|
/// The value of the code-th function A → B at the i-th element of A.
pub fn eval_at(b : FinSet, code : Int32, i : Int32) -> Int32 {
  let nb = b.length()
  b[code / ipow(nb, i) % nb]
}

///|
pub fn is_bijection(f : Fn, a : FinSet, b : FinSet) -> Bool {
  if f.length() != a.length() || a.length() != b.length() {
    return false
  }
  let seen : Array[Int32] = []
  for y in f {
    if !elem(y, b) {
      return false
    }
    if elem(y, seen) {
      return false
    }
    seen.push(y)
  }
  true
}

///|
fn elem(x : Int32, xs : Array[Int32]) -> Bool {
  for y in xs {
    if y == x {
      return true
    }
  }
  false
}

///|
pub fn count_bijections(a : FinSet, b : FinSet) -> Int32 {
  let mut c = 0
  for f in all_functions(a, b) {
    if is_bijection(f, a, b) {
      c = c + 1
    }
  }
  c
}

///|
/// The disjoint union: left elements are tagged 0, right elements 1.
pub fn coproduct(a : FinSet, b : FinSet) -> FinSet {
  let out : FinSet = []
  for x in a {
    out.push(inl(x))
  }
  for y in b {
    out.push(inr(y))
  }
  out
}

///|
pub fn inl(x : Int32) -> Int32 {
  2 * x
}

///|
pub fn inr(y : Int32) -> Int32 {
  2 * y + 1
}

///|
pub fn from_inl(z : Int32) -> Int32 {
  z / 2
}

///|
pub fn from_inr(z : Int32) -> Int32 {
  (z - 1) / 2
}

///|
pub fn is_left(z : Int32) -> Bool {
  z % 2 == 0
}

///|
/// The cartesian product: pairs are encoded as x·BASE + y.
pub fn product(a : FinSet, b : FinSet) -> FinSet {
  let out : FinSet = []
  for x in a {
    for y in b {
      out.push(pair(x, y))
    }
  }
  out
}

///|
pub fn pair(x : Int32, y : Int32) -> Int32 {
  x * 1024 + y
}

///|
pub fn pfst(p : Int32) -> Int32 {
  p / 1024
}

///|
pub fn psnd(p : Int32) -> Int32 {
  p % 1024
}

///|
/// The exponential B^A: the set of functions, represented by their codes.
pub fn exponential(a : FinSet, b : FinSet) -> FinSet {
  let total = ipow(b.length(), a.length())
  let out : FinSet = []
  for c = 0; c < total; c = c + 1 {
    out.push(c)
  }
  out
}

///|
/// Cartesian closedness 1:  C^{A⊔B} ≅ C^A × C^B  (currying at the coproduct).
pub fn curry_coproduct(a : FinSet, b : FinSet, c : FinSet) -> Fn {
  let dom = exponential(coproduct(a, b), c)
  let cod_a = exponential(a, c)
  let cod_b = exponential(b, c)
  let nc = c.length()
  let out : Fn = []
  for code in dom {
    // restriction to A and to B
    let mut ra = 0
    let mut rb = 0
    for i = 0; i < a.length(); i = i + 1 {
      let v = index_of(c, eval_at(c, code, i))
      ra = ra + v * ipow(nc, i)
    }
    for j = 0; j < b.length(); j = j + 1 {
      let v = index_of(c, eval_at(c, code, a.length() + j))
      rb = rb + v * ipow(nc, j)
    }
    out.push(pair(index_of(cod_a, ra), index_of(cod_b, rb)))
  }
  out
}

///|
fn index_of(xs : Array[Int32], x : Int32) -> Int32 {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return i
    }
  }
  abort("index_of: not found")
}

///|
/// Cartesian closedness 2:  (A × B)^C ≅ A^C × B^C.
pub fn product_exponential(a : FinSet, b : FinSet, c : FinSet) -> Fn {
  let dom = exponential(c, product(a, b))
  let cod_a = exponential(c, a)
  let cod_b = exponential(c, b)
  let out : Fn = []
  for code in dom {
    let mut ra = 0
    let mut rb = 0
    for i = 0; i < c.length(); i = i + 1 {
      let v = eval_at(product(a, b), code, i)
      ra = ra + index_of(a, pfst(v)) * ipow(a.length(), i)
      rb = rb + index_of(b, psnd(v)) * ipow(b.length(), i)
    }
    out.push(pair(index_of(cod_a, ra), index_of(cod_b, rb)))
  }
  out
}

///|
/// Cartesian closedness 3:  (C^B)^A ≅ C^{B×A}  (currying).
pub fn curry_exponential(a : FinSet, b : FinSet, c : FinSet) -> Fn {
  let inner = exponential(b, c)
  let dom = exponential(a, inner)
  let cod = exponential(product(b, a), c)
  let out : Fn = []
  for code in dom {
    // f : A -> (B -> C); build g : B x A -> C with g(b,a) = f(a)(b)
    let mut g = 0
    for k = 0; k < product(b, a).length(); k = k + 1 {
      let p = product(b, a)[k]
      let bb = pfst(p)
      let aa = psnd(p)
      let fa = eval_at(inner, code, index_of(a, aa))
      let v = eval_at(c, fa, index_of(b, bb))
      g = g + index_of(c, v) * ipow(c.length(), k)
    }
    out.push(index_of(cod, g))
  }
  out
}

///|
/// Is f : A → B a bijection onto B (verified by enumerating A's elements)?
pub fn is_bijection_onto(f : Fn, a : FinSet, b : FinSet) -> Bool {
  if f.length() != a.length() {
    return false
  }
  if a.length() != b.length() {
    return false
  }
  let seen : Array[Int32] = []
  for y in f {
    if !elem(y, b) || elem(y, seen) {
      return false
    }
    seen.push(y)
  }
  true
}

// The categorified binomial theorem.

///|
/// The k-subsets of {0,…,n−1}, as bitmasks.
pub fn subsets_of_size(n : Int32, k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for mask = 0; mask < ipow(2, n); mask = mask + 1 {
    if popcount(mask) == k {
      out.push(mask)
    }
  }
  out
}

///|
fn popcount(m : Int32) -> Int32 {
  let mut c = 0
  let mut x = m
  while x > 0 {
    c = c + x % 2
    x = x / 2
  }
  c
}

///|
fn bit(m : Int32, i : Int32) -> Int32 {
  m / ipow(2, i) % 2
}

///|
/// The domain (A ⊔ B)^{[n]}: functions from an n-element set.
pub fn functions_from_n(a : FinSet, b : FinSet, n : Int32) -> FinSet {
  let nn : FinSet = []
  for i = 0; i < n; i = i + 1 {
    nn.push(i)
  }
  exponential(nn, coproduct(a, b))
}

///|
/// A point of the right-hand side ⊔_k C(n,k) × A^{[k]} × B^{[n−k]}, encoded as
/// the single integer
///     ((k · 2^n + mask) · |A|^n + code_f) · |B|^n + code_g ,
/// which is injective because mask < 2^n, code_f < |A|^k ≤ |A|^n and
/// code_g < |B|^{n−k} ≤ |B|^n (fixed radices, so the encoding is a bijection
/// onto its image).
pub fn binomial_encode(
  n : Int32,
  k : Int32,
  mask : Int32,
  fcode : Int32,
  gcode : Int32,
  na : Int32,
  nb : Int32,
) -> Int32 {
  ((k * ipow(2, n) + mask) * ipow(na, n) + fcode) * ipow(nb, n) + gcode
}

///|
/// The categorified binomial theorem: the explicit bijection
/// (A ⊔ B)^{[n]} → ⊔_k C(n,k) × A^{[k]} × B^{[n−k]}.
pub fn binomial_bijection(a : FinSet, b : FinSet, n : Int32) -> Fn {
  let dom = functions_from_n(a, b, n)
  let cp = coproduct(a, b)
  let na = a.length()
  let nb = b.length()
  let out : Fn = []
  for code in dom {
    let mut k = 0
    let mut mask = 0
    for i = 0; i < n; i = i + 1 {
      if is_left(eval_at(cp, code, i)) {
        k = k + 1
        mask = mask + ipow(2, i)
      }
    }
    // restriction to the A-preimage (increasing order) and the B-preimage
    let mut fcode = 0
    let mut gcode = 0
    let mut fi = 0
    let mut gi = 0
    for i = 0; i < n; i = i + 1 {
      let v = eval_at(cp, code, i)
      if is_left(v) {
        fcode = fcode + index_of(a, from_inl(v)) * ipow(na, fi)
        fi = fi + 1
      } else {
        gcode = gcode + index_of(b, from_inr(v)) * ipow(nb, gi)
        gi = gi + 1
      }
    }
    out.push(binomial_encode(n, k, mask, fcode, gcode, na, nb))
  }
  out
}

///|
/// The cardinality of the right-hand side of the binomial bijection:
/// Σ_k C(n,k)·|A|^k·|B|^{n−k}.
pub fn binomial_rhs_size(na : Int32, nb : Int32, n : Int32) -> Int32 {
  let mut acc = 0
  for k = 0; k <= n; k = k + 1 {
    acc = acc + binomial(n, k) * ipow(na, k) * ipow(nb, n - k)
  }
  acc
}

// ---------------------------------------------------------------------------
// T2: graded vector spaces and Gaussian binomials.
// ---------------------------------------------------------------------------

///|
/// A finite-dimensional graded vector space over F_p, by the dimensions of
/// its homogeneous components (degrees 0, 1, 2, …).
pub type GrV = Array[Int32]

///|
/// A polynomial (Hilbert series), by coefficients in increasing degree.
pub type Poly = Array[Int32]

///|
pub fn poly_add(a : Poly, b : Poly) -> Poly {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Poly = []
  for i = 0; i < n; i = i + 1 {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    out.push(x + y)
  }
  out
}

///|
pub fn poly_mul(a : Poly, b : Poly) -> Poly {
  let out : Poly = Array::make(a.length() + b.length() - 1, 0)
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < b.length(); j = j + 1 {
      out[i + j] = out[i + j] + a[i] * b[j]
    }
  }
  out
}

///|
pub fn poly_shift(a : Poly, k : Int32) -> Poly {
  let out : Poly = []
  for i = 0; i < k; i = i + 1 {
    out.push(0)
  }
  for x in a {
    out.push(x)
  }
  out
}

///|
pub fn poly_trim(a : Poly) -> Poly {
  let mut k = a.length()
  while k > 1 && a[k - 1] == 0 {
    k = k - 1
  }
  let out : Poly = []
  for i = 0; i < k; i = i + 1 {
    out.push(a[i])
  }
  out
}

///|
pub fn poly_eq(a : Poly, b : Poly) -> Bool {
  poly_trim(a) == poly_trim(b)
}

///|
/// The Gaussian binomial coefficient [d choose n]_q as a polynomial.
pub fn gauss_binom(d : Int32, n : Int32) -> Poly {
  if n < 0 || n > d {
    return [0]
  }
  if n == 0 || n == d {
    return [1]
  }
  // [d choose n]_q = [d-1 choose n-1]_q + q^n [d-1 choose n]_q
  poly_add(
    poly_shift(gauss_binom(d - 1, n - 1), 0),
    poly_shift(gauss_binom(d - 1, n), n),
  )
}

///|
/// T2: the graded vector space V_d (one basis vector in each degree < d).
pub fn grv_standard(d : Int32) -> GrV {
  let out : GrV = []
  for i = 0; i < d; i = i + 1 {
    out.push(1)
  }
  out
}

///|
/// The Hilbert series of a graded vector space.
pub fn hilbert(v : GrV) -> Poly {
  v.copy()
}

///|
/// 同構即相同: two graded vector spaces are isomorphic iff their Hilbert
/// series coincide.
pub fn grv_iso(v : GrV, w : GrV) -> Bool {
  poly_eq(hilbert(v), hilbert(w))
}

///|
/// The explicit isomorphism: match the basis elements degree by degree.
/// Returns the list of pairs (index in v, index in w), or nothing if the
/// Hilbert series differ.
pub fn grv_isomorphism(v : GrV, w : GrV) -> Array[(Int32, Int32)] {
  if !grv_iso(v, w) {
    abort("grv_isomorphism: not isomorphic")
  }
  let out : Array[(Int32, Int32)] = []
  let mut vi = 0
  let mut wi = 0
  let n = if v.length() > w.length() { v.length() } else { w.length() }
  for d = 0; d < n; d = d + 1 {
    let dv = if d < v.length() { v[d] } else { 0 }
    let dw = if d < w.length() { w[d] } else { 0 }
    for k = 0; k < dv; k = k + 1 {
      out.push((vi + k, wi + k))
    }
    vi = vi + dv
    wi = wi + dw
  }
  out
}

///|
pub fn grv_sum(v : GrV, w : GrV) -> GrV {
  poly_add(v, w)
}

///|
pub fn grv_tensor(v : GrV, w : GrV) -> GrV {
  poly_mul(v, w)
}

///|
/// The dimension (total) of a graded vector space.
pub fn grv_dim(v : GrV) -> Int32 {
  let mut acc = 0
  for x in v {
    acc = acc + x
  }
  acc
}

///|
/// T2: Λ^n(V_d) — basis indexed by n-subsets S of {0,…,d−1}, the degree of
/// e_S being Σ_{i ∈ S} i.
pub fn exterior_power(d : Int32, n : Int32) -> GrV {
  let out : GrV = Array::make(d * (d - 1) / 2 + 1, 0)
  if n > d {
    return out
  }
  for mask = 0; mask < ipow(2, d); mask = mask + 1 {
    if popcount(mask) != n {
      continue
    }
    let mut deg = 0
    for i = 0; i < d; i = i + 1 {
      if bit(mask, i) == 1 {
        deg = deg + i
      }
    }
    out[deg] = out[deg] + 1
  }
  poly_trim(out)
}

///|
/// T2: S^n(V_d) — basis indexed by multisets of size n from {0,…,d−1},
/// i.e. by weakly increasing sequences, the degree being the sum.
pub fn symmetric_power(d : Int32, n : Int32) -> GrV {
  let maxdeg = n * (d - 1)
  let out : GrV = Array::make(maxdeg + 1, 0)
  enumerate_multisets(d, n, 0, 0, 0, out)
  out
}

///|
fn enumerate_multisets(
  d : Int32,
  n : Int32,
  idx : Int32,
  minimum : Int32,
  deg : Int32,
  out : GrV,
) -> Unit {
  if idx == n {
    out[deg] = out[deg] + 1
    return
  }
  let mut v = minimum
  while v < d {
    enumerate_multisets(d, n, idx + 1, v, deg + v, out)
    v = v + 1
  }
}

// ---------------------------------------------------------------------------
// T3: K₀ and the Euler characteristic.
// ---------------------------------------------------------------------------

///|
/// T3: the class of a bounded complex in K₀(D^b(Z)) ≅ Z, computed from the
/// chain groups.
pub fn k0_from_chains(cx : @derived.Cx) -> Int32 {
  @derived.euler_char(cx)
}

///|
/// T3: the same class computed from the homology — the two must agree
/// (Euler–Poincaré), which is precisely the statement that χ descends to
/// the derived category.
pub fn k0_from_homology(cx : @derived.Cx) -> Int32 {
  @derived.homology_euler(cx)
}

///|
/// T1: the cardinality of a finite set — the decategorification
/// K₀(FinSet) → N.
pub fn cardinality(a : FinSet) -> Int32 {
  a.length()
}

///|
/// The decategorified binomial theorem, for comparison with the bijection.
pub fn decategorified_binomial(na : Int32, nb : Int32, n : Int32) -> Bool {
  binomial_rhs_size(na, nb, n) == ipow(na + nb, n)
}
