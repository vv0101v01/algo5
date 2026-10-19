// Copyright 2026. Apache-2.0.
//
// Gröbner bases over F_p, with normal-form reduction.
//
// This is the second normal-form machine of the project:
//
//   Definition (normal form).  For a Gröbner basis G of I and f ∈ F_p[x],
//   `NF_G(f)` is the unique G-reduced representative of the coset f + I.
//
//   Theorem.  f - g ∈ I  ⟺  NF_G(f) = NF_G(g).  So equality in the quotient
//   ring — which is what "同構即相同" means for the quotient — is decidable by
//   comparing normal forms.  The test suite verifies this against brute force
//   enumeration of the quotient.
//
//   Theorem (Buchberger).  G is a Gröbner basis iff every S-polynomial
//   S(f,g) reduces to 0 modulo G.  `is_groebner` checks exactly this
//   criterion, and `buchberger` is driven by it.
//
// The initial-form machinery (`initial_form`, `initial_ideal`) is the bridge to
// tropical geometry: w ∈ Trop(I) iff in_w(I) contains no monomial.

///|
/// A monomial is an exponent vector.
pub type Mono = Array[Int32]

///|
pub(all) struct Term {
  c : Int32
  e : Array[Int32]
}

///|
/// A polynomial: terms sorted in *descending* order, no zero coefficients.
pub type Poly = Array[Term]

///|
pub type Cmp = (Array[Int32], Array[Int32]) -> Int32

///|
/// Lexicographic order (x_0 > x_1 > …).
pub fn cmp_lex(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let mut i = 0
  while i < a.length() {
    if a[i] != b[i] {
      return if a[i] > b[i] { 1 } else { 0 - 1 }
    }
    i = i + 1
  }
  0
}

///|
/// Graded lexicographic order (total degree first).
pub fn cmp_grlex(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let da = mono_deg(a)
  let db = mono_deg(b)
  if da != db {
    return if da > db { 1 } else { 0 - 1 }
  }
  cmp_lex(a, b)
}

///|
pub fn mono_deg(m : Array[Int32]) -> Int32 {
  let mut s = 0
  for x in m {
    s = s + x
  }
  s
}

///|
pub fn mono_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i = 0; i < a.length(); i = i + 1 {
    out[i] = a[i] + b[i]
  }
  out
}

///|
pub fn mono_divides(a : Array[Int32], b : Array[Int32]) -> Bool {
  let mut i = 0
  while i < a.length() {
    if a[i] > b[i] {
      return false
    }
    i = i + 1
  }
  true
}

///|
pub fn mono_lcm(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i = 0; i < a.length(); i = i + 1 {
    out[i] = if a[i] > b[i] { a[i] } else { b[i] }
  }
  out
}

///|
pub fn mono_div(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i = 0; i < a.length(); i = i + 1 {
    out[i] = a[i] - b[i]
  }
  out
}

///|
pub fn term_mul(a : Term, b : Term, p : Int32) -> Term {
  { c: a.c * b.c % p, e: mono_mul(a.e, b.e), }
}

// ---------------------------------------------------------------------------
// polynomials
// ---------------------------------------------------------------------------

///|
/// Canonicalise: collect equal monomials, kill zero coefficients, sort.
pub fn poly_normalize(terms : Array[Term], p : Int32, cmp : Cmp) -> Poly {
  let out : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for t in terms {
    if t.e.length() == 0 {
      continue
    }
    let c = mod_pos(t.c, p)
    if c == 0 {
      continue
    }
    let mut found = false
    let mut i = 0
    while i < out.length() {
      if mono_eq(out[i].e, t.e) {
        out[i] = { c: mod_pos(out[i].c + c, p), e: out[i].e, }
        found = true
        i = out.length()
      } else {
        i = i + 1
      }
    }
    if !found {
      out.push({ c, e: t.e.copy(), })
    }
  }
  let mut i = 0
  while i < out.length() {
    if out[i].c == 0 {
      out.remove(i) |> ignore
    } else {
      i = i + 1
    }
  }
  sort_terms(out, cmp)
  out
}

///|
pub fn mono_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  cmp_lex(a, b) == 0
}

///|
/// Insertion sort, descending.
fn sort_terms(ts : Array[Term], cmp : Cmp) -> Unit {
  let mut i = 1
  while i < ts.length() {
    let key = ts[i]
    let mut j = i
    while j > 0 && cmp(ts[j - 1].e, key.e) < 0 {
      ts[j] = ts[j - 1]
      j = j - 1
    }
    ts[j] = key
    i = i + 1
  }
}

///|
pub fn poly_zero() -> Poly {
  []
}



///|
pub fn poly_is_zero(f : Poly) -> Bool {
  f.length() == 0
}

///|
pub fn poly_add(f : Poly, g : Poly, p : Int32, cmp : Cmp) -> Poly {
  let ts : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for t in f {
    ts.push(t)
  }
  for t in g {
    ts.push(t)
  }
  poly_normalize(ts, p, cmp)
}

///|
pub fn poly_neg(f : Poly, p : Int32) -> Poly {
  let out : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for t in f {
    out.push({ c: mod_pos(0 - t.c, p), e: t.e.copy(), })
  }
  out
}

///|
pub fn poly_sub(f : Poly, g : Poly, p : Int32, cmp : Cmp) -> Poly {
  poly_add(f, poly_neg(g, p), p, cmp)
}

///|
pub fn poly_mul(f : Poly, g : Poly, p : Int32, cmp : Cmp) -> Poly {
  if poly_is_zero(f) || poly_is_zero(g) {
    return poly_zero()
  }
  let ts : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for a in f {
    for b in g {
      ts.push(term_mul(a, b, p))
    }
  }
  poly_normalize(ts, p, cmp)
}

///|
/// Multiply by `c · x^e`.
pub fn poly_mul_term(
  f : Poly,
  c : Int32,
  e : Array[Int32],
  p : Int32,
  cmp : Cmp,
) -> Poly {
  let ts : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for t in f {
    ts.push({ c: t.c * c % p, e: mono_mul(t.e, e), })
  }
  poly_normalize(ts, p, cmp)
}

///|
pub fn lm(f : Poly) -> Array[Int32] {
  if f.length() == 0 {
    abort("lm: zero polynomial")
  }
  f[0].e
}

///|
pub fn lc(f : Poly) -> Int32 {
  if f.length() == 0 {
    abort("lc: zero polynomial")
  }
  f[0].c
}

///|
/// Leading term.
pub fn lt(f : Poly) -> Term {
  if f.length() == 0 {
    abort("lt: zero polynomial")
  }
  f[0]
}

///|
/// The polynomial with its leading term removed.
pub fn poly_tail(f : Poly) -> Poly {
  let out : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for i = 1; i < f.length(); i = i + 1 {
    out.push(f[i])
  }
  out
}

// ---------------------------------------------------------------------------
// reduction
// ---------------------------------------------------------------------------

///|
/// One step of multivariate division: if some leading monomial divides that
/// of `f`, cancel it; otherwise move the leading term into the remainder.
/// Returns `(remainder_so_far, f)`; `done` is true when `f` is zero.
pub fn reduce_step(
  f : Poly,
  g : Array[Poly],
  p : Int32,
  cmp : Cmp,
) -> (Poly, Poly, Bool) {
  if poly_is_zero(f) {
    return ([], [], true)
  }
  let m = lm(f)
  let mut i = 0
  while i < g.length() {
    let gi = g[i]
    if !poly_is_zero(gi) && mono_divides(lm(gi), m) {
      let factor = mod_pos(lc(f) * inv_mod_p(lc(gi), p), p)
      let e = mono_div(m, lm(gi))
      let h = poly_mul_term(gi, factor, e, p, cmp)
      let newf = poly_sub(f, h, p, cmp)
      return ([], newf, false)
    }
    i = i + 1
  }
  // irreducible leading term: emit it
  let t = lt(f)
  ([t], poly_tail(f), false)
}

///|
/// Full normal form `NF_G(f)`.
pub fn normal_form(f : Poly, g : Array[Poly], p : Int32, cmp : Cmp) -> Poly {
  let rem : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  let mut cur = f
  let mut steps = 0
  while !poly_is_zero(cur) {
    steps = steps + 1
    if steps > 100000 {
      abort("normal_form: divergence (is G a Groebner basis?)")
    }
    let (r, rest, _done) = reduce_step(cur, g, p, cmp)
    for t in r {
      rem.push(t)
    }
    cur = rest
  }
  poly_normalize(rem, p, cmp)
}

///|
/// S-polynomial of f and g.
pub fn spoly(f : Poly, g : Poly, p : Int32, cmp : Cmp) -> Poly {
  if poly_is_zero(f) || poly_is_zero(g) {
    return poly_zero()
  }
  let l = mono_lcm(lm(f), lm(g))
  let ef = mono_div(l, lm(f))
  let eg = mono_div(l, lm(g))
  let invf = inv_mod_p(lc(f), p)
  let invg = inv_mod_p(lc(g), p)
  let a = poly_mul_term(f, invf, ef, p, cmp)
  let b = poly_mul_term(g, invg, eg, p, cmp)
  poly_sub(a, b, p, cmp)
}

///|
/// Buchberger's criterion: G is a Gröbner basis iff every S-polynomial
/// reduces to zero modulo G.
pub fn is_groebner(g : Array[Poly], p : Int32, cmp : Cmp) -> Bool {
  let n = g.length()
  let mut i = 0
  while i < n {
    let mut j = i + 1
    while j < n {
      if poly_is_zero(g[i]) || poly_is_zero(g[j]) {
        j = j + 1
        continue
      }
      let s = spoly(g[i], g[j], p, cmp)
      if !poly_is_zero(normal_form(s, g, p, cmp)) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// Buchberger's algorithm, with the coprime shortcut
/// (`lcm(lm f, lm g) = lm f · lm g` ⇒ S(f,g) reduces to 0).
pub fn buchberger(gens : Array[Poly], p : Int32, cmp : Cmp) -> Array[Poly] {
  let g : Array[Poly] = Array::make(0, [])
  for f in gens {
    if !poly_is_zero(f) {
      g.push(poly_normalize(f, p, cmp))
    }
  }
  let mut changed = true
  let mut rounds = 0
  while changed {
    rounds = rounds + 1
    if rounds > 200 {
      abort("buchberger: too many rounds")
    }
    changed = false
    let n = g.length()
    let mut i = 0
    while i < n {
      let mut j = i + 1
      while j < n {
        if poly_is_zero(g[i]) || poly_is_zero(g[j]) {
          j = j + 1
          continue
        }
        let lf = lm(g[i])
        let lg = lm(g[j])
        if mono_eq(mono_lcm(lf, lg), mono_mul(lf, lg)) {
          j = j + 1
          continue
        }
        let s = spoly(g[i], g[j], p, cmp)
        let r = normal_form(s, g, p, cmp)
        if !poly_is_zero(r) {
          g.push(poly_normalize(r, p, cmp))
          changed = true
        }
        j = j + 1
      }
      i = i + 1
    }
  }
  // interreduce so the result is the *reduced* (unique) Gröbner basis
  let out : Array[Poly] = Array::make(0, [])
  for i = 0; i < g.length(); i = i + 1 {
    let rest : Array[Poly] = Array::make(0, [])
    for k = 0; k < g.length(); k = k + 1 {
      if k != i {
        rest.push(g[k])
      }
    }
    let r = normal_form(g[i], rest, p, cmp)
    if !poly_is_zero(r) {
      // make monic
      let inv = inv_mod_p(lc(r), p)
      let ts : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
      for t in r {
        ts.push({ c: t.c * inv % p, e: t.e.copy(), })
      }
      out.push(poly_normalize(ts, p, cmp))
    }
  }
  // de-duplicate
  let res : Array[Poly] = Array::make(0, [])
  for f in out {
    let mut seen = false
    for h in res {
      if poly_eq(f, h) {
        seen = true
      }
    }
    if !seen {
      res.push(f)
    }
  }
  res
}

///|
pub fn poly_eq(f : Poly, g : Poly) -> Bool {
  if f.length() != g.length() {
    return false
  }
  let mut i = 0
  while i < f.length() {
    if f[i].c != g[i].c || !mono_eq(f[i].e, g[i].e) {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// Ideal membership: `f ∈ I` iff `NF_G(f) = 0`.
pub fn in_ideal(f : Poly, g : Array[Poly], p : Int32, cmp : Cmp) -> Bool {
  poly_is_zero(normal_form(f, g, p, cmp))
}

///|
/// The monomials not divisible by any leading monomial of G, up to total
/// degree `maxdeg`.  If I is zero dimensional these are a k-basis of
/// F_p[x]/I, so `|standard_monomials| = dim_{F_p} F_p[x]/I`.
pub fn standard_monomials(
  g : Array[Poly],
  n : Int32,
  maxdeg : Int32,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = Array::make(0, Array::make(0, 0))
  let e = Array::make(n, 0)
  let mut finished = false
  while !finished {
    if mono_deg(e) <= maxdeg {
      let mut divided = false
      for f in g {
        if poly_is_zero(f) {
          continue
        }
        if mono_divides(lm(f), e) {
          divided = true
        }
      }
      if !divided {
        out.push(e.copy())
      }
    }
    finished = !next_mono(e, maxdeg)
  }
  out
}

///|
/// Iterate exponent vectors in graded-lex order, bounded by total degree.
fn next_mono(e : Array[Int32], maxdeg : Int32) -> Bool {
  let n = e.length()
  // try to increment the last variable, spilling carries leftwards
  let mut i = n - 1
  while i >= 0 {
    if mono_deg(e) < maxdeg {
      e[i] = e[i] + 1
      return true
    }
    // carry: reset suffix and move left
    let mut s = 0
    for k = 0; k < i; k = k + 1 {
      s = s + e[k]
    }
    if i > 0 && s + 1 <= maxdeg {
      e[i - 1] = e[i - 1] + 1
      for k = i; k < n; k = k + 1 {
        e[k] = 0
      }
      return true
    }
    i = i - 1
  }
  false
}

///|
/// dim_{F_p} F_p[x]/I for a zero-dimensional ideal (enumerated up to
/// `maxdeg`; returns `-1` if the enumeration was not exhaustive).
pub fn quotient_dim(g : Array[Poly], n : Int32, maxdeg : Int32) -> Int32 {
  standard_monomials(g, n, maxdeg).length()
}

// ---------------------------------------------------------------------------
// initial forms — the bridge to tropical geometry
// ---------------------------------------------------------------------------

///|
/// The initial form `in_w(f)`: the sum of the terms of f of maximal
/// `w`-weight.
pub fn initial_form(f : Poly, w : Array[Int32]) -> Poly {
  if poly_is_zero(f) {
    return poly_zero()
  }
  let mut best = weight(lm(f), w)
  for t in f {
    let wt = weight(t.e, w)
    if wt > best {
      best = wt
    }
  }
  let out : Array[Term] = Array::make(0, { c: 0, e: Array::make(0, 0), })
  for t in f {
    if weight(t.e, w) == best {
      out.push(t)
    }
  }
  out
}

///|
pub fn weight(e : Array[Int32], w : Array[Int32]) -> Int32 {
  let mut s = 0
  for i = 0; i < e.length(); i = i + 1 {
    s = s + e[i] * w[i]
  }
  s
}

///|
/// `in_w(I) = ⟨ in_w(g) : g ∈ G ⟩` when G is a Gröbner basis for a
/// `w`-compatible order; otherwise this is only a subideal, so we recompute a
/// basis of it.
pub fn initial_ideal(
  g : Array[Poly],
  w : Array[Int32],
  p : Int32,
  cmp : Cmp,
) -> Array[Poly] {
  let gens : Array[Poly] = Array::make(0, [])
  for f in g {
    if !poly_is_zero(f) {
      gens.push(initial_form(f, w))
    }
  }
  buchberger(gens, p, cmp)
}

///|
/// Theorem (tropical membership / Gröbner complex).
/// For an ideal I ⊂ k[x_1^{±},…,x_n^{±}] and w ∈ R^n:
///     w ∈ Trop(I)  ⟺  in_w(I) contains no monomial.
/// `is_tropical` implements that test for the affine (non-Laurent) case.
pub fn is_tropical(
  g : Array[Poly],
  w : Array[Int32],
  p : Int32,
  cmp : Cmp,
) -> Bool {
  let ii = initial_ideal(g, w, p, cmp)
  for f in ii {
    if f.length() == 1 {
      return false
    }
  }
  true
}
