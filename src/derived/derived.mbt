///|
/// 導範疇 (DERIVED CATEGORIES) — chain complexes, homology, mapping cones,
/// quasi-isomorphisms, and the derived functors Ext and Tor, machine-checked.
///
/// Setting
/// -------
/// We work in Ch(Z): bounded complexes of finitely generated *free* abelian
/// groups
///
///     C :  … → C_{n+1} —d_{n+1}→ C_n —d_n→ C_{n−1} → … ,   d_n d_{n+1} = 0,
///
/// each C_n ≅ Z^{r_n} presented by the integer matrix of d_n.  All
/// computation is exact integer linear algebra (Smith / Hermite normal forms
/// from `src/nf`), so "isomorphism" of finitely generated abelian groups is
/// decided by equality of Smith normal forms — 同構即相同.
///
/// Theorems implemented here
/// -------------------------
/// T1 (Homology).  H_n(C) = ker d_n / im d_{n+1}.  Computed by taking a basis
/// of ker d_n from the Smith normal form of d_n (the columns of V beyond the
/// rank), expressing im d_{n+1} in that basis via the dual rows of V^{−1},
/// and reading off H_n = coker of the resulting matrix — so H_n is returned
/// as a *presentation matrix*, and two homology groups are isomorphic iff
/// their presentation matrices are so.
/// T2 (Euler–Poincaré).  χ(C) = Σ_n (−1)^n rk C_n = Σ_n (−1)^n rk H_n(C).
/// T3 (Mapping cone / triangulated structure).  For a chain map f : C → D,
///     Cone(f)_n = D_n ⊕ C_{n−1},   d = [ d_D  f ; 0  −d_C ],
/// and f is a quasi-isomorphism ⟺ Cone(f) is acyclic.  Equivalently the
/// triangle C → D → Cone(f) → C[1] is distinguished, and its homology is a
/// long exact sequence, so Σ_n (−1)^n (rk H_n D − rk H_n Cone − rk H_n C) = 0.
/// T4 (Splitting over Z).  Z has global dimension 1, hence every bounded
/// complex of free abelian groups is isomorphic in D^b(Z) to the direct sum
/// of its homology groups placed in their degrees:
///     C ≅ ⊕_n H_n(C)[n]  in D^b(Z),
/// realised by the "split complex" built from the invariant factors of the
/// differentials, and — for two-term complexes — by an *explicitly
/// constructed* quasi-isomorphism.
/// T5 (Künneth).  For complexes C, D of free abelian groups,
///     H_n(C ⊗ D) ≅ ⊕_{i+j=n} H_i(C) ⊗ H_j(D)  ⊕  ⊕_{i+j=n−1} Tor_1(H_i C, H_j D).
/// T6 (Ext and Tor).  With P = [Z —×n→ Z] the free resolution of Z/n,
///     Tor_i^Z(Z/n, Z/m) = H_i(P_n ⊗ P_m) = Z/gcd(n,m) for i = 0,1 and 0 else;
///     Ext^i_Z(Z/n, Z)   = H^i(Hom(P_n, Z)) = Z/n for i = 1 and 0 else;
/// and more generally the universal coefficient theorem
///     0 → Ext^1(H_{n−1} C, Z) → H^n(Hom(C, Z)) → Hom(H_n C, Z) → 0.
pub type Mat = Array[Array[Int32]]

// ---------------------------------------------------------------------------
// Exact integer linear algebra.
// ---------------------------------------------------------------------------

///|
pub fn mat_zeros(m : Int32, n : Int32) -> Mat {
  let out : Mat = []
  for i = 0; i < m; i = i + 1 {
    out.push(Array::make(n, 0))
  }
  out
}

///|
pub fn mat_rows(a : Mat) -> Int32 {
  a.length()
}

///|
pub fn mat_cols(a : Mat) -> Int32 {
  if a.length() == 0 {
    0
  } else {
    a[0].length()
  }
}

///|
pub fn mat_add(a : Mat, b : Mat) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < mat_cols(a); j = j + 1 {
      row.push(a[i][j] + b[i][j])
    }
    out.push(row)
  }
  out
}

///|
pub fn mat_neg(a : Mat) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < mat_cols(a); j = j + 1 {
      row.push(0 - a[i][j])
    }
    out.push(row)
  }
  out
}


///|
pub fn mat_scale(a : Mat, k : Int32) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < mat_cols(a); j = j + 1 {
      row.push(a[i][j] * k)
    }
    out.push(row)
  }
  out
}

///|
pub fn mat_is_zero(a : Mat) -> Bool {
  for i = 0; i < mat_rows(a); i = i + 1 {
    for j = 0; j < mat_cols(a); j = j + 1 {
      if a[i][j] != 0 {
        return false
      }
    }
  }
  true
}

///|
pub fn mat_eq(a : Mat, b : Mat) -> Bool {
  if mat_rows(a) != mat_rows(b) || mat_cols(a) != mat_cols(b) {
    return false
  }
  for i = 0; i < mat_rows(a); i = i + 1 {
    for j = 0; j < mat_cols(a); j = j + 1 {
      if a[i][j] != b[i][j] {
        return false
      }
    }
  }
  true
}

///|
/// Horizontal concatenation [a | b] (same number of rows).
pub fn mat_hstack(a : Mat, b : Mat) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < mat_cols(a); j = j + 1 {
      row.push(a[i][j])
    }
    for j = 0; j < mat_cols(b); j = j + 1 {
      row.push(b[i][j])
    }
    out.push(row)
  }
  out
}

///|
/// Vertical concatenation [a ; b] (same number of columns).
pub fn mat_vstack(a : Mat, b : Mat) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    out.push(a[i].copy())
  }
  for i = 0; i < mat_rows(b); i = i + 1 {
    out.push(b[i].copy())
  }
  out
}

///|
/// Kronecker product a ⊗ b (blocks a_{ij}·b).
pub fn mat_kron(a : Mat, b : Mat) -> Mat {
  let rb = mat_rows(b)
  let cb = mat_cols(b)
  let out = mat_zeros(mat_rows(a) * rb, mat_cols(a) * cb)
  for i = 0; i < mat_rows(a); i = i + 1 {
    for j = 0; j < mat_cols(a); j = j + 1 {
      for k = 0; k < rb; k = k + 1 {
        for l = 0; l < cb; l = l + 1 {
          out[i * rb + k][j * cb + l] = a[i][j] * b[k][l]
        }
      }
    }
  }
  out
}

///|
/// Determinant by cofactor expansion (exact; complexes here are small).
pub fn det_int(a : Mat) -> Int32 {
  let n = mat_rows(a)
  if n == 0 {
    return 1
  }
  if n == 1 {
    return a[0][0]
  }
  let mut acc = 0
  for j = 0; j < n; j = j + 1 {
    if a[0][j] != 0 {
      let s = if j % 2 == 0 { 1 } else { 0 - 1 }
      acc = acc + s * a[0][j] * det_int(mat_minor(a, 0, j))
    }
  }
  acc
}

///|
/// The (i,j) minor: delete row i and column j.
pub fn mat_minor(a : Mat, i0 : Int32, j0 : Int32) -> Mat {
  let out : Mat = []
  for i = 0; i < mat_rows(a); i = i + 1 {
    if i == i0 {
      continue
    }
    let row : Array[Int32] = []
    for j = 0; j < mat_cols(a); j = j + 1 {
      if j == j0 {
        continue
      }
      row.push(a[i][j])
    }
    out.push(row)
  }
  out
}

///|
/// The inverse of a unimodular matrix (det = ±1), via the adjugate.
pub fn inverse_unimodular(a : Mat) -> Mat {
  let d = det_int(a)
  if d != 1 && d != 0 - 1 {
    abort("inverse_unimodular: matrix is not unimodular")
  }
  let n = mat_rows(a)
  let out = mat_zeros(n, n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      let s = if (i + j) % 2 == 0 { 1 } else { 0 - 1 }
      // (i,j) entry of the inverse = (1/det) · cofactor_{ji}
      out[i][j] = d * s * det_int(mat_minor(a, j, i))
    }
  }
  out
}

///|
/// A basis of ker(a) (columns) together with the dual projection P (rows of
/// V^{−1}) satisfying P · K = identity.  `ncols` is the number of columns of
/// a, which must be given explicitly since a may have zero rows.
pub fn kernel_basis(a : Mat, ncols : Int32) -> (Mat, Mat) {
  let n = ncols
  if mat_rows(a) == 0 {
    // d_0 : C_0 -> 0 has kernel all of C_0
    return (@nf.mat_identity(n), @nf.mat_identity(n))
  }
  let s = @nf.smith_normal_form(a)
  let diag = @nf.snf_diag(s)
  let v = @nf.snf_v(s)
  let mut r = 0
  for d in diag {
    if d != 0 {
      r = r + 1
    }
  }
  let k = n - r
  let kmat = mat_zeros(n, k)
  let vinv = inverse_unimodular(v)
  let pmat = mat_zeros(k, n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < k; j = j + 1 {
      kmat[i][j] = v[i][r + j]
    }
  }
  for i = 0; i < k; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      pmat[i][j] = vinv[r + i][j]
    }
  }
  (kmat, pmat)
}

// ---------------------------------------------------------------------------
// Chain complexes.
// ---------------------------------------------------------------------------

///|
pub(all) struct Cx {
  ranks : Array[Int32]
  /// d[n] is the matrix of d_n : C_n → C_{n−1} (ranks[n−1] rows, ranks[n]
  /// columns); d[0] has zero rows.
  d : Array[Mat]
}

///|
pub fn cx_new(ranks : Array[Int32], d : Array[Mat]) -> Cx {
  { ranks, d, }
}

///|
/// The complex with the given ranks and zero differentials.
pub fn cx_zero(ranks : Array[Int32]) -> Cx {
  let d : Array[Mat] = []
  d.push(mat_zeros(0, ranks[0]))
  for n = 1; n < ranks.length(); n = n + 1 {
    d.push(mat_zeros(ranks[n - 1], ranks[n]))
  }
  { ranks, d, }
}

///|
/// A two-term complex 0 → Z^{r1} —m→ Z^{r0} → 0.
pub fn cx_two_term(r0 : Int32, m : Mat, r1 : Int32) -> Cx {
  let d : Array[Mat] = []
  d.push(mat_zeros(0, r0))
  d.push(m)
  { ranks: [r0, r1], d, }
}

///|
pub fn cx_len(cx : Cx) -> Int32 {
  cx.ranks.length()
}

///|
/// The matrix of d_n, with the correct shape outside the range of degrees.
pub fn cx_diff(cx : Cx, n : Int32) -> Mat {
  if n >= 0 && n < cx.d.length() {
    cx.d[n]
  } else if n == cx.d.length() {
    mat_zeros(cx.ranks[n - 1], 0)
  } else {
    mat_zeros(0, 0)
  }
}

///|
/// The rank of C_n (0 outside the range of degrees).
pub fn cx_rank(cx : Cx, n : Int32) -> Int32 {
  if n >= 0 && n < cx.ranks.length() {
    cx.ranks[n]
  } else {
    0
  }
}

///|
/// The chain condition d_n · d_{n+1} = 0.
pub fn is_complex(cx : Cx) -> Bool {
  for n = 0; n + 1 < cx.d.length(); n = n + 1 {
    if !(mat_is_zero(@nf.mat_mul(cx.d[n], cx.d[n + 1]))) {
      return false
    }
  }
  true
}

///|
pub fn euler_char(cx : Cx) -> Int32 {
  let mut acc = 0
  for n = 0; n < cx.ranks.length(); n = n + 1 {
    if n % 2 == 0 {
      acc = acc + cx.ranks[n]
    } else {
      acc = acc - cx.ranks[n]
    }
  }
  acc
}


// ---------------------------------------------------------------------------
// T1: homology, as a presentation matrix for each degree.
// ---------------------------------------------------------------------------

///|
/// T1: H_n(C) for every n, as a presentation matrix M with H_n = coker(M).
pub fn homology(cx : Cx) -> Array[Mat] {
  let out : Array[Mat] = []
  for n = 0; n < cx.ranks.length(); n = n + 1 {
    let a = cx_diff(cx, n)
    let b = cx_diff(cx, n + 1)
    let (_k, p) = kernel_basis(a, cx.ranks[n])
    // im(d_{n+1}) expressed in a basis of ker(d_n)
    out.push(@nf.mat_mul(p, b))
  }
  out
}

///|
/// The free rank of H_n(C).
pub fn homology_rank(cx : Cx, n : Int32) -> Int32 {
  @nf.coker_rank(homology(cx)[n])
}

///|
/// The torsion invariant factors of H_n(C) (the d_i > 1).
pub fn homology_torsion(cx : Cx, n : Int32) -> Array[Int32] {
  torsion_factors(homology(cx)[n])
}

///|
pub fn torsion_factors(m : Mat) -> Array[Int32] {
  let out : Array[Int32] = []
  for d in @nf.invariant_factors(m) {
    if d > 1 {
      out.push(d)
    }
  }
  out
}

///|
pub fn is_acyclic(cx : Cx) -> Bool {
  for m in homology(cx) {
    if @nf.coker_rank(m) != 0 {
      return false
    }
    if torsion_factors(m).length() != 0 {
      return false
    }
  }
  true
}

///|
/// T2: Σ (−1)^n rk H_n(C).
pub fn homology_euler(cx : Cx) -> Int32 {
  let mut acc = 0
  for n = 0; n < cx.ranks.length(); n = n + 1 {
    let r = homology_rank(cx, n)
    if n % 2 == 0 {
      acc = acc + r
    } else {
      acc = acc - r
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// Chain maps, cones, shifts (T3).
// ---------------------------------------------------------------------------

///|
pub(all) struct CM {
  /// f[n] : C_n → D_n (ranks_D[n] rows, ranks_C[n] columns).
  f : Array[Mat]
}

///|
pub fn cm_new(f : Array[Mat]) -> CM {
  { f, }
}

///|
pub fn cm_get(m : CM, src : Cx, dst : Cx, n : Int32) -> Mat {
  if n >= 0 && n < m.f.length() {
    m.f[n]
  } else {
    mat_zeros(cx_rank(dst, n), cx_rank(src, n))
  }
}

///|
pub fn is_chain_map(src : Cx, dst : Cx, m : CM) -> Bool {
  for n = 0; n < src.ranks.length() + 1; n = n + 1 {
    let lhs = @nf.mat_mul(cx_diff(dst, n), cm_get(m, src, dst, n))
    let rhs = @nf.mat_mul(cm_get(m, src, dst, n - 1), cx_diff(src, n))
    if !(mat_eq(lhs, rhs)) {
      return false
    }
  }
  true
}

///|
/// T3: Cone(f)_n = D_n ⊕ C_{n−1} with d = [ d_D  f ; 0  −d_C ].
pub fn cone(src : Cx, dst : Cx, m : CM) -> Cx {
  let n = src.ranks.length()
  let ranks : Array[Int32] = []
  let d : Array[Mat] = []
  // degrees 0..n: Cone_n = D_n (+) C_{n-1} still carries the top term C_{n-1}
  for k = 0; k < n + 1; k = k + 1 {
    ranks.push(cx_rank(dst, k) + cx_rank(src, k - 1))
  }
  for k = 0; k < n + 1; k = k + 1 {
    let dd = cx_diff(dst, k)
    let ff = cm_get(m, src, dst, k - 1)
    let top = mat_hstack(dd, ff)
    let dc = cx_diff(src, k - 1)
    let bottom = mat_hstack(mat_zeros(mat_rows(dc), mat_cols(dd)), mat_neg(dc))
    d.push(mat_vstack(top, bottom))
  }
  { ranks, d, }
}

///|
/// T3: f is a quasi-isomorphism iff its cone is acyclic.
pub fn is_quasi_iso(src : Cx, dst : Cx, m : CM) -> Bool {
  is_acyclic(cone(src, dst, m))
}

///|
/// The shift C[k] : C[k]_n = C_{n−k} with differential (−1)^k d.
pub fn shift(cx : Cx, k : Int32) -> Cx {
  if k < 0 {
    abort("shift: only non-negative shifts are implemented")
  }
  let ranks : Array[Int32] = []
  let d : Array[Mat] = []
  for i = 0; i < k; i = i + 1 {
    ranks.push(0)
  }
  for r in cx.ranks {
    ranks.push(r)
  }
  for i = 0; i < k; i = i + 1 {
    d.push(mat_zeros(0, 0))
  }
  let s = if k % 2 == 0 { 1 } else { 0 - 1 }
  for i = 0; i < cx.d.length(); i = i + 1 {
    d.push(mat_scale(cx.d[i], s))
  }
  { ranks, d, }
}

///|
/// The identity chain map.
pub fn cm_id(cx : Cx) -> CM {
  let f : Array[Mat] = []
  for r in cx.ranks {
    f.push(@nf.mat_identity(r))
  }
  cm_new(f)
}

// ---------------------------------------------------------------------------
// T4: splitting.
// ---------------------------------------------------------------------------

///|
/// The homology groups of C as (free rank, torsion factors).
pub fn homology_data(cx : Cx) -> Array[(Int32, Array[Int32])] {
  let out : Array[(Int32, Array[Int32])] = []
  for m in homology(cx) {
    out.push((@nf.coker_rank(m), torsion_factors(m)))
  }
  out
}

///|
/// T4: the split complex ⊕_n H_n(C)[n], as a complex of free abelian groups.
/// Each free summand Z of H_n sits in degree n; each torsion summand Z/d of
/// H_n is realised by the two-term complex Z —×d→ Z sitting in degrees
/// n+1 → n (so the split complex has one more degree than C when the top
/// homology has torsion).
pub fn split_cx(cx : Cx) -> Cx {
  let hd = homology_data(cx)
  let n = hd.length()
  let a = Array::make(n + 1, 0)
  let t : Array[Array[Int32]] = Array::make(n + 1, [])
  for k = 0; k < n; k = k + 1 {
    let (r, ts) = hd[k]
    a[k] = r
    t[k] = ts
  }
  let ranks : Array[Int32] = []
  for k = 0; k < n + 1; k = k + 1 {
    let prev = if k >= 1 { t[k - 1].length() } else { 0 }
    ranks.push(a[k] + t[k].length() + prev)
  }
  let d : Array[Mat] = []
  for k = 0; k < n + 1; k = k + 1 {
    if k == 0 {
      d.push(mat_zeros(0, ranks[0]))
      continue
    }
    let m = mat_zeros(ranks[k - 1], ranks[k])
    // the last t[k-1] columns are the sources of the torsion of H_{k-1}
    let prev = t[k - 1]
    let col0 = a[k] + t[k].length()
    let row0 = a[k - 1]
    for i = 0; i < prev.length(); i = i + 1 {
      m[row0 + i][col0 + i] = prev[i]
    }
    d.push(m)
  }
  { ranks, d, }
}

///|
/// T4 for two-term complexes: the split complex together with an *explicit*
/// quasi-isomorphism split(C) → C, built from the Smith normal form
/// U·d·V = D of the differential (kernel generators = columns of V beyond
/// the rank; cokernel generators = columns of U^{−1}).
pub fn split_2term(cx : Cx) -> (Cx, CM) {
  if cx.ranks.length() != 2 {
    abort("split_2term: not a two-term complex")
  }
  let dm = cx.d[1]
  let s = @nf.smith_normal_form(dm)
  let diag = @nf.snf_diag(s)
  let u = @nf.snf_u(s)
  let v = @nf.snf_v(s)
  let uinv = inverse_unimodular(u)
  let vinv = inverse_unimodular(v)
  let r0 = cx.ranks[0]
  let r1 = cx.ranks[1]
  let mut rk = 0
  for d in diag {
    if d != 0 {
      rk = rk + 1
    }
  }
  let free_part = r0 - rk
  let kernel_dim = r1 - rk
  // torsion generators: the d_i > 1
  let ts : Array[Int32] = []
  let ts_idx : Array[Int32] = []
  for i = 0; i < rk; i = i + 1 {
    if diag[i] > 1 {
      ts.push(diag[i])
      ts_idx.push(i)
    }
  }
  let t = ts.length()
  let sranks = [free_part + t, kernel_dim + t]
  let sd : Array[Mat] = []
  sd.push(mat_zeros(0, sranks[0]))
  let sdm = mat_zeros(sranks[0], sranks[1])
  for i = 0; i < t; i = i + 1 {
    sdm[free_part + i][kernel_dim + i] = ts[i]
  }
  sd.push(sdm)
  let split = { ranks: sranks, d: sd, }
  // f_1 : S_1 = Z^{kernel_dim} ⊕ Z^t → C_1
  let f1 = mat_zeros(r1, sranks[1])
  for j = 0; j < kernel_dim; j = j + 1 {
    for i = 0; i < r1; i = i + 1 {
      f1[i][j] = v[i][rk + j]
    }
  }
  for j = 0; j < t; j = j + 1 {
    for i = 0; i < r1; i = i + 1 {
      f1[i][kernel_dim + j] = v[i][ts_idx[j]]
    }
  }
  // f_0 : S_0 = Z^{free_part} ⊕ Z^t → C_0
  let f0 = mat_zeros(r0, sranks[0])
  for j = 0; j < free_part; j = j + 1 {
    for i = 0; i < r0; i = i + 1 {
      f0[i][j] = uinv[i][rk + j]
    }
  }
  for j = 0; j < t; j = j + 1 {
    for i = 0; i < r0; i = i + 1 {
      f0[i][free_part + j] = uinv[i][ts_idx[j]]
    }
  }
  let _ = vinv
  let f : Array[Mat] = []
  f.push(f0)
  f.push(f1)
  (split, cm_new(f))
}

// ---------------------------------------------------------------------------
// T5: tensor products of complexes, and the Künneth formula.
// ---------------------------------------------------------------------------

///|
/// T5: (C ⊗ D)_n = ⊕_{i+j=n} C_i ⊗ D_j with
/// d(c ⊗ d) = d_C c ⊗ d + (−1)^{deg c} c ⊗ d_D d.
pub fn tensor_cx(a : Cx, b : Cx) -> Cx {
  let na = a.ranks.length()
  let nb = b.ranks.length()
  let n = na + nb - 1
  let ranks : Array[Int32] = []
  for k = 0; k < n; k = k + 1 {
    let mut acc = 0
    for i = 0; i < na; i = i + 1 {
      let j = k - i
      if j >= 0 && j < nb {
        acc = acc + a.ranks[i] * b.ranks[j]
      }
    }
    ranks.push(acc)
  }
  let d : Array[Mat] = []
  for k = 0; k < n; k = k + 1 {
    let m = mat_zeros(if k > 0 { ranks[k - 1] } else { 0 }, ranks[k])
    // iterate over source blocks (i,j) with i + j = k
    let mut ccol = 0
    for i = 0; i < na; i = i + 1 {
      let j = k - i
      if j < 0 || j >= nb {
        continue
      }
      // target block (i-1, j): d_C_i ⊗ I
      if i - 1 >= 0 && k - 1 >= 0 {
        let blk = mat_kron(cx_diff(a, i), @nf.mat_identity(b.ranks[j]))
        let mut rrow = 0
        for i2 = 0; i2 < na; i2 = i2 + 1 {
          let j2 = k - 1 - i2
          if j2 < 0 || j2 >= nb {
            continue
          }
          if i2 == i - 1 && j2 == j {
            for x = 0; x < mat_rows(blk); x = x + 1 {
              for y = 0; y < mat_cols(blk); y = y + 1 {
                m[rrow + x][ccol + y] = m[rrow + x][ccol + y] + blk[x][y]
              }
            }
          }
          rrow = rrow + a.ranks[i2] * b.ranks[j2]
        }
      }
      // target block (i, j-1): (-1)^i I ⊗ d_D_j
      if j - 1 >= 0 && k - 1 >= 0 {
        let s = if i % 2 == 0 { 1 } else { 0 - 1 }
        let blk = mat_scale(
          mat_kron(@nf.mat_identity(a.ranks[i]), cx_diff(b, j)),
          s,
        )
        let mut rrow = 0
        for i2 = 0; i2 < na; i2 = i2 + 1 {
          let j2 = k - 1 - i2
          if j2 < 0 || j2 >= nb {
            continue
          }
          if i2 == i && j2 == j - 1 {
            for x = 0; x < mat_rows(blk); x = x + 1 {
              for y = 0; y < mat_cols(blk); y = y + 1 {
                m[rrow + x][ccol + y] = m[rrow + x][ccol + y] + blk[x][y]
              }
            }
          }
          rrow = rrow + a.ranks[i2] * b.ranks[j2]
        }
      }
      ccol = ccol + a.ranks[i] * b.ranks[j]
    }
    d.push(m)
  }
  { ranks, d, }
}

///|
/// The dual (Hom(−, Z)) complex, re-indexed as a chain complex:
/// degree n carries Hom(C_{N−n}, Z), so H_n of the result is the cohomology
/// H^{N−n}(Hom(C, Z)).
pub fn dual_cx(a : Cx) -> Cx {
  let n = a.ranks.length()
  let ranks : Array[Int32] = []
  for k = 0; k < n; k = k + 1 {
    ranks.push(a.ranks[n - 1 - k])
  }
  let d : Array[Mat] = []
  for k = 0; k < n; k = k + 1 {
    // d_k : Hom(C_{N-k}) -> Hom(C_{N-k+1}) is the transpose of d_{N-k+1}
    let idx = n - k
    d.push(@nf.mat_transpose(cx_diff(a, idx)))
  }
  { ranks, d, }
}

// ---------------------------------------------------------------------------
// Finitely generated abelian groups as presentation matrices.
// ---------------------------------------------------------------------------

///|
/// The group Z^rank ⊕ ⊕_i Z/factors_i as a presentation matrix.
pub fn grp(rank : Int32, factors : Array[Int32]) -> Mat {
  let k = factors.length()
  let m = mat_zeros(rank + k, k)
  for i = 0; i < k; i = i + 1 {
    m[i][i] = factors[i]
  }
  m
}

///|
pub fn grp_rank(g : Mat) -> Int32 {
  @nf.coker_rank(g)
}

///|
pub fn grp_factors(g : Mat) -> Array[Int32] {
  torsion_factors(g)
}

///|
/// 同構即相同: two finitely generated abelian groups are isomorphic iff their
/// Smith normal forms agree.
pub fn grp_iso(g : Mat, h : Mat) -> Bool {
  @nf.abelian_iso(g, h)
}

///|
/// gcd(|a|,|b|).  Delegates to `@tl.igcd`: one implementation, shared.
pub fn gcd_pos(a : Int32, b : Int32) -> Int32 {
  @tl.igcd(a, b)
}

///|
/// (Z^{r1} ⊕ ⊕_a Z/d_a) ⊗ (Z^{r2} ⊕ ⊕_b Z/e_b) ≅
/// Z^{r1 r2} ⊕ (⊕_a Z/d_a)^{r2} ⊕ (⊕_b Z/e_b)^{r1} ⊕ ⊕_{a,b} Z/gcd(d_a,e_b).
pub fn grp_tensor(g : Mat, h : Mat) -> Mat {
  let r1 = grp_rank(g)
  let r2 = grp_rank(h)
  let d = grp_factors(g)
  let e = grp_factors(h)
  let rank = r1 * r2
  let facs : Array[Int32] = []
  for a in d {
    for i = 0; i < r2; i = i + 1 {
      facs.push(a)
    }
  }
  for b in e {
    for i = 0; i < r1; i = i + 1 {
      facs.push(b)
    }
  }
  for a in d {
    for b in e {
      facs.push(gcd_pos(a, b))
    }
  }
  grp(rank, facs)
}

///|
/// Tor_1^Z(G, H) ≅ ⊕_{a,b} Z/gcd(d_a, e_b) (the free parts contribute 0).
pub fn grp_tor(g : Mat, h : Mat) -> Mat {
  let d = grp_factors(g)
  let e = grp_factors(h)
  let facs : Array[Int32] = []
  for a in d {
    for b in e {
      facs.push(gcd_pos(a, b))
    }
  }
  grp(0, facs)
}

///|
/// The direct sum of two groups, as a presentation matrix.
pub fn grp_sum(g : Mat, h : Mat) -> Mat {
  let r = grp_rank(g) + grp_rank(h)
  let facs : Array[Int32] = []
  for f in grp_factors(g) {
    facs.push(f)
  }
  for f in grp_factors(h) {
    facs.push(f)
  }
  grp(r, facs)
}

///|
/// T6: Tor_i^Z(Z/n, Z/m) via the tensor product of the two free resolutions
/// [Z —×n→ Z] ⊗ [Z —×m→ Z].
pub fn tor_of(n : Int32, m : Int32) -> Array[Mat] {
  let pn = cx_two_term(1, [[n]], 1)
  let pm = cx_two_term(1, [[m]], 1)
  homology(tensor_cx(pn, pm))
}

///|
/// T6: Ext^i_Z(Z/n, Z) via Hom(P_n, Z) for the free resolution P_n.
pub fn ext_of(n : Int32) -> Array[Mat] {
  let pn = cx_two_term(1, [[n]], 1)
  homology(dual_cx(pn))
}

///|
/// T5: the Künneth formula's prediction for H_n(C ⊗ D).
pub fn kunneth_predict(a : Cx, b : Cx) -> Array[Mat] {
  let ha = homology(a)
  let hb = homology(b)
  let n = a.ranks.length() + b.ranks.length() - 1
  let out : Array[Mat] = []
  for k = 0; k < n; k = k + 1 {
    let mut acc = grp(0, [])
    for i = 0; i < ha.length(); i = i + 1 {
      for j = 0; j < hb.length(); j = j + 1 {
        if i + j == k {
          acc = grp_sum(acc, grp_tensor(ha[i], hb[j]))
        }
        if i + j == k - 1 {
          acc = grp_sum(acc, grp_tor(ha[i], hb[j]))
        }
      }
    }
    out.push(acc)
  }
  out
}
