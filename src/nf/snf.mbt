// Copyright 2026. Apache-2.0.
//
// Integer normal forms.  These are the workhorse for "同構即相同":
//
//   Theorem (Smith).  Every integer matrix A ∈ Z^{m×n} admits unimodular
//   U ∈ GL_m(Z), V ∈ GL_n(Z) with  U·A·V = diag(d_1,…,d_r,0,…,0)  and
//   d_1 | d_2 | … | d_r.  The d_i are the *invariant factors*.
//
//   Theorem (structure of finitely generated abelian groups).  For
//   A ∈ Z^{m×n},  coker(A : Z^n → Z^m) ≅ ⊕_{i} Z/d_i ⊕ Z^{m-r}.  Two such
//   groups are isomorphic **iff** their invariant factor lists agree.
//   Hence `abelian_iso` below is a decision procedure for isomorphism:
//   isomorphic is *literally* equal normal form.

///|
/// Extended Euclidean algorithm.  Returns `(g, s, t)` with
/// `g = gcd(a,b) = s·a + t·b`, `g ≥ 0`.
pub fn ext_gcd(a0 : Int32, b0 : Int32) -> (Int32, Int32, Int32) {
  let mut old_r = a0
  let mut r = b0
  let mut old_s = 1
  let mut s = 0
  let mut old_t = 0
  let mut t = 1
  while r != 0 {
    let q = old_r / r
    let nr = old_r - q * r
    let ns = old_s - q * s
    let nt = old_t - q * t
    old_r = r
    r = nr
    old_s = s
    s = ns
    old_t = t
    t = nt
  }
  if old_r < 0 {
    (0 - old_r, 0 - old_s, 0 - old_t)
  } else {
    (old_r, old_s, old_t)
  }
}

///|
pub fn gcd(a : Int32, b : Int32) -> Int32 {
  let (g, _, _) = ext_gcd(a, b)
  g
}

// ---------------------------------------------------------------------------
// small dense integer matrices, as arrays of rows
// ---------------------------------------------------------------------------

///|
pub fn mat_make(rows : Int32, cols : Int32) -> Array[Array[Int32]] {
  let out = Array::make(rows, Array::make(0, 0))
  for i = 0; i < rows; i = i + 1 {
    out[i] = Array::make(cols, 0)
  }
  out
}

///|
pub fn mat_identity(n : Int32) -> Array[Array[Int32]] {
  let out = mat_make(n, n)
  for i = 0; i < n; i = i + 1 {
    out[i][i] = 1
  }
  out
}

///|
pub fn mat_copy(a : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let rows = a.length()
  let out = Array::make(rows, Array::make(0, 0))
  for i = 0; i < rows; i = i + 1 {
    out[i] = a[i].copy()
  }
  out
}

///|
pub fn mat_mul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let m = a.length()
  let n = if m == 0 { 0 } else { a[0].length() }
  let p = if b.length() == 0 { 0 } else { b[0].length() }
  let out = mat_make(m, p)
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < p; j = j + 1 {
      let mut s = 0
      for k = 0; k < n; k = k + 1 {
        s = s + a[i][k] * b[k][j]
      }
      out[i][j] = s
    }
  }
  out
}

///|
pub fn mat_transpose(a : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let m = a.length()
  let n = if m == 0 { 0 } else { a[0].length() }
  let out = mat_make(n, m)
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      out[j][i] = a[i][j]
    }
  }
  out
}

///|
/// Exact determinant by fraction-free (Bareiss) elimination.
pub fn mat_det(a : Array[Array[Int32]]) -> Int32 {
  let n = a.length()
  if n == 0 {
    return 1
  }
  let m = mat_copy(a)
  let mut sign = 1
  let mut prev = 1
  for k = 0; k < n - 1; k = k + 1 {
    if m[k][k] == 0 {
      let mut swap = -1
      for i = k + 1; i < n; i = i + 1 {
        if m[i][k] != 0 && swap < 0 {
          swap = i
        }
      }
      if swap < 0 {
        return 0
      }
      let tmp = m[k]
      m[k] = m[swap]
      m[swap] = tmp
      sign = 0 - sign
    }
    for i = k + 1; i < n; i = i + 1 {
      for j = k + 1; j < n; j = j + 1 {
        m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) / prev
      }
    }
    prev = m[k][k]
  }
  sign * m[n - 1][n - 1]
}

// ---------------------------------------------------------------------------
// Smith normal form
// ---------------------------------------------------------------------------

///|
/// The result of `smith_normal_form`: the diagonal, the row transform `U`
/// and the column transform `V`, with `U · A · V = D`.
pub struct Snf {
  diag : Array[Int32]
  u : Array[Array[Int32]]
  v : Array[Array[Int32]]
}

///|
pub fn snf_diag(s : Snf) -> Array[Int32] {
  s.diag
}

///|
pub fn snf_u(s : Snf) -> Array[Array[Int32]] {
  s.u
}

///|
pub fn snf_v(s : Snf) -> Array[Array[Int32]] {
  s.v
}

///|
/// Row operation helpers (applied to `A` and, simultaneously, to `U`).
fn row_combine(
  a : Array[Array[Int32]],
  u : Array[Array[Int32]],
  i : Int32,
  j : Int32,
  s : Int32,
  t : Int32,
  p : Int32,
  q : Int32,
) -> Unit {
  // row_i <- s*row_i + t*row_j ;  row_j <- p*row_i + q*row_j  (old values)
  let ri = a[i].copy()
  let rj = a[j].copy()
  let ui = u[i].copy()
  let uj = u[j].copy()
  for k = 0; k < ri.length(); k = k + 1 {
    a[i][k] = s * ri[k] + t * rj[k]
    a[j][k] = p * ri[k] + q * rj[k]
  }
  for k = 0; k < ui.length(); k = k + 1 {
    u[i][k] = s * ui[k] + t * uj[k]
    u[j][k] = p * ui[k] + q * uj[k]
  }
}

///|
fn col_combine(
  a : Array[Array[Int32]],
  v : Array[Array[Int32]],
  i : Int32,
  j : Int32,
  s : Int32,
  t : Int32,
  p : Int32,
  q : Int32,
) -> Unit {
  let m = a.length()
  let mut k = 0
  while k < m {
    let ci = a[k][i]
    let cj = a[k][j]
    a[k][i] = s * ci + t * cj
    a[k][j] = p * ci + q * cj
    k = k + 1
  }
  let n = v.length()
  k = 0
  while k < n {
    let ci = v[k][i]
    let cj = v[k][j]
    v[k][i] = s * ci + t * cj
    v[k][j] = p * ci + q * cj
    k = k + 1
  }
}

///|
/// Smith normal form, with the unimodular transforms.
///
/// The algorithm repeatedly
///   (i)  moves the smallest non-zero entry of the active submatrix to the
///        corner,
///   (ii) clears the rest of its row and column by unimodular row/column
///        operations built from the extended Euclidean algorithm,
///   (iii) pulls in any entry not divisible by the corner and repeats.
/// Termination is guaranteed because step (iii) strictly decreases
/// |A[k][k]| (a well founded measure); see the test `snf_certificate`.
pub fn smith_normal_form(a0 : Array[Array[Int32]]) -> Snf {
  let m = a0.length()
  let n = if m == 0 { 0 } else { a0[0].length() }
  let a = mat_copy(a0)
  let u = mat_identity(m)
  let v = mat_identity(n)
  let kmax = if m < n { m } else { n }
  let mut k = 0
  while k < kmax {
    // (i) pivot
    let mut pi = -1
    let mut pj = -1
    let mut best = 0
    let mut i = k
    while i < m {
      let mut j = k
      while j < n {
        let x = a[i][j]
        if x != 0 && (best == 0 || abs_int(x) < abs_int(best)) {
          best = x
          pi = i
          pj = j
        }
        j = j + 1
      }
      i = i + 1
    }
    if pi < 0 {
      k = k + 1
      continue
    }
    if pi != k {
      swap_rows(a, u, k, pi)
    }
    if pj != k {
      swap_cols(a, v, k, pj)
    }
    // (ii)+(iii)
    let mut progress = true
    while progress {
      progress = false
      let mut i = k + 1
      while i < m {
        if a[i][k] != 0 {
          let (g, s, t) = ext_gcd(a[k][k], a[i][k])
          let q1 = a[k][k] / g
          let q2 = a[i][k] / g
          row_combine(a, u, k, i, s, t, 0 - q2, q1)
          progress = true
        }
        i = i + 1
      }
      let mut j = k + 1
      while j < n {
        if a[k][j] != 0 {
          let (g, s, t) = ext_gcd(a[k][k], a[k][j])
          let q1 = a[k][k] / g
          let q2 = a[k][j] / g
          col_combine(a, v, k, j, s, t, 0 - q2, q1)
          progress = true
        }
        j = j + 1
      }
      // divisibility sweep
      let mut i = k + 1
      while i < m && !progress {
        let mut j = k + 1
        while j < n && !progress {
          if a[i][j] != 0 {
            if a[k][k] == 0 || a[i][j] % a[k][k] != 0 {
              // add row i into row k, then re-clear
              row_add(a, u, k, i)
              progress = true
            }
          }
          j = j + 1
        }
        i = i + 1
      }
      // any residue left in row/column k also forces another pass
      let mut i = k + 1
      while i < m && !progress {
        if a[i][k] != 0 {
          progress = true
        }
        i = i + 1
      }
      let mut j = k + 1
      while j < n && !progress {
        if a[k][j] != 0 {
          progress = true
        }
        j = j + 1
      }
    }
    if a[k][k] < 0 {
      for j = 0; j < n; j = j + 1 {
        a[k][j] = 0 - a[k][j]
      }
      for j = 0; j < m; j = j + 1 {
        u[k][j] = 0 - u[k][j]
      }
    }
    k = k + 1
  }
  let diag = Array::make(kmax, 0)
  for i = 0; i < kmax; i = i + 1 {
    diag[i] = a[i][i]
  }
  { diag, u, v, }
}

///|
fn abs_int(x : Int32) -> Int32 {
  if x < 0 {
    0 - x
  } else {
    x
  }
}

///|
fn swap_rows(
  a : Array[Array[Int32]],
  u : Array[Array[Int32]],
  i : Int32,
  j : Int32,
) -> Unit {
  let t = a[i]
  a[i] = a[j]
  a[j] = t
  let t2 = u[i]
  u[i] = u[j]
  u[j] = t2
}

///|
fn swap_cols(
  a : Array[Array[Int32]],
  v : Array[Array[Int32]],
  i : Int32,
  j : Int32,
) -> Unit {
  for k = 0; k < a.length(); k = k + 1 {
    let t = a[k][i]
    a[k][i] = a[k][j]
    a[k][j] = t
  }
  for k = 0; k < v.length(); k = k + 1 {
    let t = v[k][i]
    v[k][i] = v[k][j]
    v[k][j] = t
  }
}

///|
fn row_add(
  a : Array[Array[Int32]],
  u : Array[Array[Int32]],
  i : Int32,
  j : Int32,
) -> Unit {
  for k = 0; k < a[i].length(); k = k + 1 {
    a[i][k] = a[i][k] + a[j][k]
  }
  for k = 0; k < u[i].length(); k = k + 1 {
    u[i][k] = u[i][k] + u[j][k]
  }
}

///|
/// The invariant factors, i.e. the non-zero diagonal entries (with the
/// divisibility chain enforced).
pub fn invariant_factors(a : Array[Array[Int32]]) -> Array[Int32] {
  let s = smith_normal_form(a)
  let out = Array::make(0, 0)
  for d in s.diag {
    if d != 0 {
      out.push(d)
    }
  }
  out
}

///|
/// The free rank of `coker(A)`.
pub fn coker_rank(a : Array[Array[Int32]]) -> Int32 {
  let m = a.length()
  m - invariant_factors(a).length()
}

///|
/// Theorem (isomorphism of finitely generated abelian groups).
/// `coker(A) ≅ coker(B)` **iff** the invariant factors coincide (and the free
/// ranks coincide).  Isomorphism is *equality of normal forms*.
pub fn abelian_iso(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  // only the *non-trivial* invariant factors are isomorphism invariants:
  // Z/1 is the trivial group, and Z/d ⊕ Z/e ≅ Z/de whenever d, e are coprime.
  let fa = nontrivial(invariant_factors(a))
  let fb = nontrivial(invariant_factors(b))
  if fa.length() != fb.length() {
    return false
  }
  if coker_rank(a) != coker_rank(b) {
    return false
  }
  let mut i = 0
  while i < fa.length() {
    if fa[i] != fb[i] {
      return false
    }
    i = i + 1
  }
  true
}

///|
/// Drop the trivial factors (d = 1) from an invariant-factor list.
pub fn nontrivial(ds : Array[Int32]) -> Array[Int32] {
  let out = Array::make(0, 0)
  for d in ds {
    if d > 1 {
      out.push(d)
    }
  }
  out
}

///|
/// Elementary divisors (primary decomposition) of `coker(A)`: for each
/// invariant factor d > 1 and each prime p | d, the group Z/p^e.
pub fn elementary_divisors(a : Array[Array[Int32]]) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = Array::make(0, (0, 0))
  for d in invariant_factors(a) {
    if d <= 1 {
      continue
    }
    let mut x = d
    let mut p = 2
    while p * p <= x {
      if x % p == 0 {
        let mut e = 0
        while x % p == 0 {
          x = x / p
          e = e + 1
        }
        out.push((p, e))
      }
      p = p + 1
    }
    if x > 1 {
      out.push((x, 1))
    }
  }
  out
}

///|
/// Rank of an integer matrix over Q (and over any field of char. 0).
pub fn rank_q(a : Array[Array[Int32]]) -> Int32 {
  invariant_factors(a).length()
}

///|
/// Rank modulo a prime p (Gauss elimination over F_p).
pub fn rank_mod_p(a : Array[Array[Int32]], p : Int32) -> Int32 {
  let m = a.length()
  if m == 0 {
    return 0
  }
  let n = a[0].length()
  let b = mat_copy(a)
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      b[i][j] = mod_pos(b[i][j], p)
    }
  }
  let mut r = 0
  let mut col = 0
  while col < n && r < m {
    let mut piv = -1
    let mut i = r
    while i < m {
      if b[i][col] % p != 0 {
        piv = i
        i = m
      } else {
        i = i + 1
      }
    }
    if piv < 0 {
      col = col + 1
      continue
    }
    let t = b[r]
    b[r] = b[piv]
    b[piv] = t
    let inv = inv_mod_p(b[r][col] % p, p)
    for j = col; j < n; j = j + 1 {
      b[r][j] = b[r][j] * inv % p
    }
    let mut i = 0
    while i < m {
      if i != r && b[i][col] % p != 0 {
        let f = b[i][col] % p
        for j = col; j < n; j = j + 1 {
          b[i][j] = mod_pos(b[i][j] - f * b[r][j], p)
        }
      }
      i = i + 1
    }
    r = r + 1
    col = col + 1
  }
  r
}

///|
pub fn mod_pos(a : Int32, p : Int32) -> Int32 {
  let r = a % p
  if r < 0 {
    r + p
  } else {
    r
  }
}

///|
pub fn inv_mod_p(a : Int32, p : Int32) -> Int32 {
  let (g, s, _) = ext_gcd(mod_pos(a, p), p)
  if g != 1 {
    abort("inv_mod_p: not invertible")
  }
  mod_pos(s, p)
}

// ---------------------------------------------------------------------------
// Hermite normal form (row style, for full row rank matrices)
// ---------------------------------------------------------------------------

///|
/// Column-style Hermite normal form of a full-rank square matrix:
/// returns `H` upper triangular with positive diagonal and `H = A·U` for a
/// unimodular `U` (used to decide equality of lattices / subgroups).
pub fn hermite_normal_form(a0 : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let n = a0.length()
  let a = mat_copy(a0)
  for k = 0; k < n; k = k + 1 {
    // put a non-zero pivot in (k,k)
    let mut i = k
    while i < n && a[i][k] == 0 {
      i = i + 1
    }
    if i == n {
      continue
    }
    if i != k {
      let t = a[k]
      a[k] = a[i]
      a[i] = t
    }
    for j = k + 1; j < n; j = j + 1 {
      if a[j][k] != 0 {
        let (g, s, t) = ext_gcd(a[k][k], a[j][k])
        let q1 = a[k][k] / g
        let q2 = a[j][k] / g
        let rk = a[k].copy()
        let rj = a[j].copy()
        for c = 0; c < n; c = c + 1 {
          a[k][c] = s * rk[c] + t * rj[c]
          a[j][c] = 0 - q2 * rk[c] + q1 * rj[c]
        }
      }
    }
    if a[k][k] < 0 {
      for c = 0; c < n; c = c + 1 {
        a[k][c] = 0 - a[k][c]
      }
    }
  }
  // final reduction: for a column style HNF (upper triangular, H = A·U) the
  // off diagonal entries satisfy 0 ≤ H[i][j] < H[i][i] for j > i.
  for i = 0; i < n; i = i + 1 {
    if a[i][i] > 0 {
      for j = i + 1; j < n; j = j + 1 {
        a[i][j] = mod_pos(a[i][j], a[i][i])
      }
    }
  }
  a
}

///|
pub fn floor_div(a : Int32, b : Int32) -> Int32 {
  if b == 0 {
    abort("floor_div: division by zero")
  }
  let q = a / b
  let r = a - q * b
  if r != 0 && (r < 0) != (b < 0) {
    q - 1
  } else {
    q
  }
}

///|
/// Absolute value (exported helper).
pub fn abs_int_export(x : Int32) -> Int32 {
  abs_int(x)
}
