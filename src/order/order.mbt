// Copyright 2026. Apache-2.0.
//
// Finite orders (posets), distributive lattices, completions.
//
// Theorems implemented / verified by the tests:
//
//   T1 (Birkhoff's representation theorem).  Every finite distributive
//       lattice L is isomorphic to the lattice O(J(L)) of order ideals of its
//       poset of join-irreducible elements, via
//            φ : L → O(J(L)),   φ(x) = { j ∈ J(L) : j ≤ x }.
//       Conversely J(O(P)) ≅ P.  `birkhoff_iso` builds φ and the tests check
//       it is an order isomorphism *and* that it preserves ∨ and ∧.  Hence
//       "同構即相同": two finite distributive lattices are isomorphic iff the
//       posets J(L) are isomorphic, and the *canonical form* of L is the
//       poset J(L).
//
//   T2 (Dedekind–MacNeille).  DM(P) = { A ⊆ P : A = (A^u)^l } ordered by
//       inclusion is the smallest complete lattice containing P; the embedding
//       x ↦ ↓x preserves all joins and meets that exist in P.  `dm_completion`
//       computes it and the test checks completeness + preservation.
//
//   T3 (hook-length formula for forests).  For a rooted forest poset P,
//       e(P) = #linear extensions = |P|! / Π_v |subtree(v)|.
//       Verified against brute-force enumeration of linear extensions.

///|
/// A finite poset, given by its reflexive-transitive relation matrix.
pub(all) struct Poset {
  n : Int32
  le : Array[Array[Bool]]
}


///|
/// Build a poset from a list of strict covering pairs, then close
/// reflexively and transitively.
pub fn poset_from_pairs(n : Int32, pairs : Array[(Int32, Int32)]) -> Poset {
  let m = Array::make(n, Array::make(0, false))
  for i = 0; i < n; i = i + 1 {
    m[i] = Array::make(n, false)
  }
  for (a, b) in pairs {
    if a < 0 || a >= n || b < 0 || b >= n {
      abort("poset_from_pairs: index out of range")
    }
    m[a][b] = true
  }
  let p = { n, le: m, }
  transitive_closure(p)
}

///|
/// Floyd–Warshall transitive closure.
pub fn transitive_closure(p : Poset) -> Poset {
  let n = p.n
  let le = Array::make(n, Array::make(0, false))
  for i = 0; i < n; i = i + 1 {
    le[i] = p.le[i].copy()
    le[i][i] = true
  }
  let mut k = 0
  while k < n {
    let mut i = 0
    while i < n {
      if le[i][k] {
        let mut j = 0
        while j < n {
          if le[k][j] {
            le[i][j] = true
          }
          j = j + 1
        }
      }
      i = i + 1
    }
    k = k + 1
  }
  { n, le, }
}

///|
/// The covering relation (transitive reduction) — the Hasse diagram.
pub fn transitive_reduction(p : Poset) -> Array[Array[Bool]] {
  let n = p.n
  let out = Array::make(n, Array::make(0, false))
  for i = 0; i < n; i = i + 1 {
    out[i] = Array::make(n, false)
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if i != j && p.le[i][j] {
        let mut intermediate = false
        let mut k = 0
        while k < n {
          if k != i && k != j && p.le[i][k] && p.le[k][j] {
            intermediate = true
          }
          k = k + 1
        }
        out[i][j] = !intermediate
      }
    }
  }
  out
}

///|
/// Axioms: reflexive, antisymmetric, transitive.
pub fn is_poset(p : Poset) -> Bool {
  let n = p.n
  for i = 0; i < n; i = i + 1 {
    if !p.le[i][i] {
      return false
    }
    for j = 0; j < n; j = j + 1 {
      if p.le[i][j] && p.le[j][i] && i != j {
        return false
      }
      for k = 0; k < n; k = k + 1 {
        if p.le[i][j] && p.le[j][k] && !p.le[i][k] {
          return false
        }
      }
    }
  }
  true
}

///|
/// Least upper bound of a subset (given as a Boolean mask), or -1.
pub fn lub(p : Poset, mask : Array[Bool]) -> Int32 {
  let cands : Array[Int32] = Array::make(0, 0)
  for i = 0; i < p.n; i = i + 1 {
    let mut all = true
    for j = 0; j < p.n; j = j + 1 {
      if mask[j] && !p.le[j][i] {
        all = false
      }
    }
    if all {
      cands.push(i)
    }
  }
  // least element of the upper bounds
  let mut best = -1
  for c in cands {
    let mut least = true
    for d in cands {
      if !p.le[c][d] {
        least = false
      }
    }
    if least {
      best = c
    }
  }
  best
}

///|
pub fn glb(p : Poset, mask : Array[Bool]) -> Int32 {
  let cands : Array[Int32] = Array::make(0, 0)
  for i = 0; i < p.n; i = i + 1 {
    let mut all = true
    for j = 0; j < p.n; j = j + 1 {
      if mask[j] && !p.le[i][j] {
        all = false
      }
    }
    if all {
      cands.push(i)
    }
  }
  let mut best = -1
  for c in cands {
    let mut greatest = true
    for d in cands {
      if !p.le[d][c] {
        greatest = false
      }
    }
    if greatest {
      best = c
    }
  }
  best
}

///|
pub fn join(p : Poset, a : Int32, b : Int32) -> Int32 {
  let mask = Array::make(p.n, false)
  mask[a] = true
  mask[b] = true
  lub(p, mask)
}

///|
pub fn meet(p : Poset, a : Int32, b : Int32) -> Int32 {
  let mask = Array::make(p.n, false)
  mask[a] = true
  mask[b] = true
  glb(p, mask)
}

///|
/// Every pair has a join and a meet.
pub fn is_lattice(p : Poset) -> Bool {
  for i = 0; i < p.n; i = i + 1 {
    for j = 0; j < p.n; j = j + 1 {
      if join(p, i, j) < 0 || meet(p, i, j) < 0 {
        return false
      }
    }
  }
  true
}

///|
/// Distributive law x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z) for all triples.
pub fn is_distributive(p : Poset) -> Bool {
  for x = 0; x < p.n; x = x + 1 {
    for y = 0; y < p.n; y = y + 1 {
      for z = 0; z < p.n; z = z + 1 {
        let yz = join(p, y, z)
        if yz < 0 {
          return false
        }
        let lhs = meet(p, x, yz)
        let a = meet(p, x, y)
        let b = meet(p, x, z)
        if a < 0 || b < 0 {
          return false
        }
        let rhs = join(p, a, b)
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// Modular law is weaker than distributivity; checked for completeness.
pub fn is_modular(p : Poset) -> Bool {
  for x = 0; x < p.n; x = x + 1 {
    for y = 0; y < p.n; y = y + 1 {
      for z = 0; z < p.n; z = z + 1 {
        if !p.le[z][x] {
          continue
        }
        let a = join(p, z, meet(p, x, y))
        let b = meet(p, x, join(p, z, y))
        if a < 0 || b < 0 || a != b {
          return false
        }
      }
    }
  }
  true
}

///|
/// Join-irreducible elements.  `x` is join-irreducible iff it is not the
/// minimum and it covers exactly one element, i.e. the set
/// `{y : y < x, y ≺ x}` has size one.  (In a chain *every* non-minimum
/// element is join-irreducible — counting all elements below instead of
/// covers would be wrong.)
pub fn join_irreducibles(p : Poset) -> Array[Int32] {
  let cov = transitive_reduction(p)
  let out = Array::make(0, 0)
  for i = 0; i < p.n; i = i + 1 {
    let mut covers = 0
    for j = 0; j < p.n; j = j + 1 {
      if cov[j][i] {
        covers = covers + 1
      }
    }
    if covers == 1 {
      out.push(i)
    }
  }
  out
}

///|
/// The sub-poset induced on a subset of elements.
pub fn induced(p : Poset, idxs : Array[Int32]) -> Poset {
  let m = idxs.length()
  let le = Array::make(m, Array::make(0, false))
  for i = 0; i < m; i = i + 1 {
    le[i] = Array::make(m, false)
  }
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      le[i][j] = p.le[idxs[i]][idxs[j]]
    }
  }
  { n: m, le, }
}

///|
/// All downsets (order ideals) of a poset, as Boolean masks.
/// Exponential: only for |P| ≤ ~18.
pub fn order_ideals(p : Poset) -> Array[Array[Bool]] {
  let out : Array[Array[Bool]] = Array::make(0, Array::make(0, false))
  let n = p.n
  let total = 1 << n
  let mut bits = 0
  while bits < total {
    let mask = Array::make(n, false)
    for i = 0; i < n; i = i + 1 {
      mask[i] = (bits & (1 << i)) != 0
    }
    let mut ok = true
    for i = 0; i < n; i = i + 1 {
      if !mask[i] {
        continue
      }
      for j = 0; j < n; j = j + 1 {
        if p.le[j][i] && !mask[j] {
          ok = false
        }
      }
    }
    if ok {
      out.push(mask)
    }
    bits = bits + 1
  }
  out
}

///|
/// The lattice O(P) of order ideals of P, ordered by inclusion.
/// Elements are indexed in the order returned by `order_ideals`.
pub fn ideal_lattice(p : Poset) -> Poset {
  let ideals = order_ideals(p)
  let m = ideals.length()
  let le = Array::make(m, Array::make(0, false))
  for i = 0; i < m; i = i + 1 {
    le[i] = Array::make(m, false)
    for j = 0; j < m; j = j + 1 {
      let mut sub = true
      for k = 0; k < p.n; k = k + 1 {
        if ideals[i][k] && !ideals[j][k] {
          sub = false
        }
      }
      le[i][j] = sub
    }
  }
  { n: m, le, }
}

///|
/// Birkhoff's map φ : L → O(J(L)),  φ(x) = { j ∈ J(L) : j ≤ x }.
/// Returns (J(L) as indices of L, the list of ideals in the same order as
/// `order_ideals(J(L))`, and the index of φ(x) for each x ∈ L).
pub fn birkhoff_iso(
  l : Poset,
) -> (Array[Int32], Array[Array[Bool]], Array[Int32]) {
  let jl = join_irreducibles(l)
  let sub = induced(l, jl)
  let ideals = order_ideals(sub)
  let phi = Array::make(l.n, 0)
  for x = 0; x < l.n; x = x + 1 {
    let mut found = -1
    for i = 0; i < ideals.length(); i = i + 1 {
      let mut eq = true
      for k = 0; k < sub.n; k = k + 1 {
        let in_ideal = ideals[i][k]
        let le = l.le[jl[k]][x]
        if in_ideal != le {
          eq = false
        }
      }
      if eq {
        found = i
      }
    }
    phi[x] = found
  }
  (jl, ideals, phi)
}

///|
/// Verify that Birkhoff's φ is a bijective ∨/∧-preserving order embedding
/// onto O(J(L)) — i.e. that L ≅ O(J(L)) as lattices.
pub fn check_birkhoff(l : Poset) -> Bool {
  let (jl, ideals, phi) = birkhoff_iso(l)
  // (a) φ is defined everywhere and injective
  let seen = Array::make(ideals.length(), false)
  for x = 0; x < l.n; x = x + 1 {
    if phi[x] < 0 {
      return false
    }
    if seen[phi[x]] {
      return false
    }
    seen[phi[x]] = true
  }
  // (b) surjective onto the ideals
  for i = 0; i < ideals.length(); i = i + 1 {
    if !seen[i] {
      return false
    }
  }
  // (c) order embedding and its inverse
  for x = 0; x < l.n; x = x + 1 {
    for y = 0; y < l.n; y = y + 1 {
      if l.le[x][y] != subset_eq(ideals[phi[x]], ideals[phi[y]]) {
        return false
      }
    }
  }
  // (d) preserves join and meet
  for x = 0; x < l.n; x = x + 1 {
    for y = 0; y < l.n; y = y + 1 {
      let j = join(l, x, y)
      let m = meet(l, x, y)
      if j < 0 || m < 0 {
        return false
      }
      // join in O(J) is union, meet is intersection
      let un = union_mask(ideals[phi[x]], ideals[phi[y]])
      let it = inter_mask(ideals[phi[x]], ideals[phi[y]])
      if !mask_eq(un, ideals[phi[j]]) {
        return false
      }
      if !mask_eq(it, ideals[phi[m]]) {
        return false
      }
    }
  }
  let _ = jl
  true
}

///|
pub fn subset_eq(a : Array[Bool], b : Array[Bool]) -> Bool {
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] && !b[i] {
      return false
    }
  }
  true
}

///|
pub fn union_mask(a : Array[Bool], b : Array[Bool]) -> Array[Bool] {
  let out = Array::make(a.length(), false)
  for i = 0; i < a.length(); i = i + 1 {
    out[i] = a[i] || b[i]
  }
  out
}

///|
pub fn inter_mask(a : Array[Bool], b : Array[Bool]) -> Array[Bool] {
  let out = Array::make(a.length(), false)
  for i = 0; i < a.length(); i = i + 1 {
    out[i] = a[i] && b[i]
  }
  out
}

///|
pub fn mask_eq(a : Array[Bool], b : Array[Bool]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Dedekind–MacNeille completion
// ---------------------------------------------------------------------------

///|
/// Upper bounds of a mask.
pub fn upper_bounds(p : Poset, mask : Array[Bool]) -> Array[Bool] {
  let out = Array::make(p.n, false)
  for i = 0; i < p.n; i = i + 1 {
    let mut all = true
    for j = 0; j < p.n; j = j + 1 {
      if mask[j] && !p.le[j][i] {
        all = false
      }
    }
    out[i] = all
  }
  out
}

///|
pub fn lower_bounds(p : Poset, mask : Array[Bool]) -> Array[Bool] {
  let out = Array::make(p.n, false)
  for i = 0; i < p.n; i = i + 1 {
    let mut all = true
    for j = 0; j < p.n; j = j + 1 {
      if mask[j] && !p.le[i][j] {
        all = false
      }
    }
    out[i] = all
  }
  out
}

///|
/// The Dedekind–MacNeille completion DM(P): the set of cuts
/// A = (A^u)^l, ordered by inclusion.  Returns the list of cuts and, for
/// every x ∈ P, the index of its principal ideal ↓x.
pub fn dm_completion(p : Poset) -> (Array[Array[Bool]], Array[Int32]) {
  let n = p.n
  let cuts : Array[Array[Bool]] = Array::make(0, Array::make(0, false))
  let total = 1 << n
  let mut bits = 0
  while bits < total {
    let mask = Array::make(n, false)
    for i = 0; i < n; i = i + 1 {
      mask[i] = (bits & (1 << i)) != 0
    }
    let cl = lower_bounds(p, upper_bounds(p, mask))
    if mask_eq(cl, mask) {
      cuts.push(mask)
    }
    bits = bits + 1
  }
  let embed = Array::make(n, 0)
  for x = 0; x < n; x = x + 1 {
    let mut idx = -1
    for i = 0; i < cuts.length(); i = i + 1 {
      let mut eq = true
      for j = 0; j < n; j = j + 1 {
        let want = p.le[j][x]
        if cuts[i][j] != want {
          eq = false
        }
      }
      if eq {
        idx = i
      }
    }
    embed[x] = idx
  }
  (cuts, embed)
}

///|
/// The lattice structure on the cuts (order = inclusion).
pub fn dm_lattice(p : Poset) -> Poset {
  let (cuts, _) = dm_completion(p)
  let m = cuts.length()
  let le = Array::make(m, Array::make(0, false))
  for i = 0; i < m; i = i + 1 {
    le[i] = Array::make(m, false)
    for j = 0; j < m; j = j + 1 {
      le[i][j] = subset_eq(cuts[i], cuts[j])
    }
  }
  { n: m, le, }
}

///|
/// Checks that DM(P) is a complete lattice, that x ↦ ↓x embeds P, and that
/// the embedding preserves every join/meet that exists in P.
pub fn check_dm(p : Poset) -> Bool {
  let (cuts, embed) = dm_completion(p)
  let dml = dm_lattice(p)
  if !is_lattice(dml) {
    return false
  }
  // embedding is injective and order reflecting
  for x = 0; x < p.n; x = x + 1 {
    if embed[x] < 0 {
      return false
    }
    for y = 0; y < p.n; y = y + 1 {
      if p.le[x][y] != dml.le[embed[x]][embed[y]] {
        return false
      }
    }
  }
  // preservation of existing joins/meets
  for x = 0; x < p.n; x = x + 1 {
    for y = 0; y < p.n; y = y + 1 {
      let j = join(p, x, y)
      let m = meet(p, x, y)
      if j >= 0 {
        let jd = join(dml, embed[x], embed[y])
        if jd != embed[j] {
          return false
        }
      }
      if m >= 0 {
        let md = meet(dml, embed[x], embed[y])
        if md != embed[m] {
          return false
        }
      }
    }
  }
  let _ = cuts
  true
}

// ---------------------------------------------------------------------------
// linear extensions
// ---------------------------------------------------------------------------

///|
/// Number of linear extensions, by brute-force enumeration of permutations.
pub fn count_linear_extensions(p : Poset) -> Int32 {
  let n = p.n
  let used = Array::make(n, false)
  let count : Ref[Int32] = { val: 0, }
  count_ext(p, used, 0, n, count)
  count.val
}

///|
fn count_ext(
  p : Poset,
  used : Array[Bool],
  depth : Int32,
  n : Int32,
  count : Ref[Int32],
) -> Unit {
  if depth == n {
    count.val = count.val + 1
    return
  }
  for i = 0; i < n; i = i + 1 {
    if used[i] {
      continue
    }
    // i is admissible iff every j ≺ i (j ≠ i, j ≤ i) is already used
    let mut ok = true
    for j = 0; j < n; j = j + 1 {
      if j != i && p.le[j][i] && !used[j] {
        ok = false
      }
    }
    if ok {
      used[i] = true
      count_ext(p, used, depth + 1, n, count)
      used[i] = false
    }
  }
}

///|
/// Hook-length formula for forests:
/// e(P) = n! / Π_v |↓v|  where ↓v is the principal ideal (subtree) of v.
pub fn hook_length_forest(p : Poset) -> Int32 {
  let n = p.n
  let mut denom = 1
  for v = 0; v < n; v = v + 1 {
    let mut h = 0
    for j = 0; j < n; j = j + 1 {
      if p.le[v][j] {
        h = h + 1
      }
    }
    denom = denom * h
  }
  let mut num = 1
  for k = 2; k <= n; k = k + 1 {
    num = num * k
  }
  num / denom
}

// ---------------------------------------------------------------------------
// the dominance order on partitions
// ---------------------------------------------------------------------------

///|
/// All partitions of n as non-increasing integer lists, in lex order.
pub fn partitions(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = Array::make(0, Array::make(0, 0))
  let cur : Array[Int32] = Array::make(0, 0)
  gen_partitions(n, n, cur, out)
  out
}

///|
fn gen_partitions(
  rem : Int32,
  maxpart : Int32,
  cur : Array[Int32],
  out : Array[Array[Int32]],
) -> Unit {
  if rem == 0 {
    out.push(cur.copy())
    return
  }
  let mut k = if rem < maxpart { rem } else { maxpart }
  while k >= 1 {
    cur.push(k)
    gen_partitions(rem - k, k, cur, out)
    cur.pop() |> ignore
    k = k - 1
  }
}

///|
/// Dominance (majorisation) order: λ ≥ μ iff Σ_{i≤k} λ_i ≥ Σ_{i≤k} μ_i
/// for every k.  This is a lattice (a classical theorem) that is *not*
/// distributive in general.
pub fn dominance_poset(n : Int32) -> Poset {
  let ps = partitions(n)
  let m = ps.length()
  let le = Array::make(m, Array::make(0, false))
  for i = 0; i < m; i = i + 1 {
    le[i] = Array::make(m, false)
  }
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      le[i][j] = dominates(ps[i], ps[j])
    }
  }
  { n: m, le, }
}

///|
pub fn dominates(lam : Array[Int32], mu : Array[Int32]) -> Bool {
  let kmax = if lam.length() > mu.length() { lam.length() } else { mu.length() }
  let mut sl = 0
  let mut sm = 0
  for k = 0; k < kmax; k = k + 1 {
    if k < lam.length() {
      sl = sl + lam[k]
    }
    if k < mu.length() {
      sm = sm + mu[k]
    }
    if sl < sm {
      return false
    }
  }
  true
}
