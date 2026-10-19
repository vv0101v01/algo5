// ---------------------------------------------------------------------------
// 層化 (sheafification), part 2: presheaves, the plus construction, stalks.
//
// Notation.  A presheaf F on a site C is a contravariant functor C^op -> Set;
// concretely, a set F(U) of sections for every object and restriction maps
// F(a) : F(cod a) -> F(dom a) for every arrow a, with F(id) = id and
// F(a ∘ b) = F(b) ∘ F(a).
//
// The sheaf condition for a covering family {a_i : U_i -> U} is that
//
//        F(U) -> ∏_i F(U_i) ⇉ ∏_{i,j} F(U_i ×_U U_j)                    (†)
//
// is an equalizer: a family of sections that agrees on all overlaps comes from
// a unique section of F(U).
//
// The plus construction.  For a cover R = {U_i -> U} let Match(R, F) be the
// set of matching families.  One puts
//
//        F⁺(U) = colim_{R ∈ Cov(U)} Match(R, F),
//
// the colimit over the (filtered) system of covers ordered by refinement, the
// transition maps being restriction of matching families.  Two matching
// families are identified when they agree after restriction to a common
// refinement.  Then:
//
//   T1  F⁺ is always separated, and F^# := F⁺⁺ is always a sheaf;
//       η : F -> F^# is the sheafification (unit of the adjunction).
//   T3  F is a sheaf  ⟺  η_F : F -> F^# is an isomorphism.
//   T4  Hom(F^#, G) ≅ Hom(F, G) for every sheaf G: sheafification is left
//       adjoint to the forgetful inclusion Sh(C) ↪ PSh(C).
// ---------------------------------------------------------------------------

///|
/// A presheaf of sets: `fibers[u]` sections over the object u, numbered
/// 0, 1, ..., and `res[a]` the restriction along the arrow a.
pub(all) struct PSh {
  fibers : Array[Int]
  res : Array[Array[Int]]
}

///|
pub fn psh(fibers : Array[Int], res : Array[Array[Int]]) -> PSh {
  { fibers, res, }
}

///|
/// Functoriality: F(id) = id and F(a ∘ b) = F(b) ∘ F(a).
pub fn psh_ok(site : Site, f : PSh) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    let e = id_arrow(site, u)
    for s = 0; s < f.fibers[u]; s = s + 1 {
      if f.res[e][s] != s {
        return false
      }
    }
  }
  for a = 0; a < site.arrows.length(); a = a + 1 {
    for b = 0; b < site.arrows.length(); b = b + 1 {
      let ab = compose(site, a, b)
      if ab < 0 {
        continue
      }
      let cod = site.arrows[a].cod
      for s = 0; s < f.fibers[cod]; s = s + 1 {
        let lhs = f.res[ab][s]
        let rhs = f.res[b][f.res[a][s]]
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// The map F(cod a) -> F(dom a) as an array.
pub fn restr(f : PSh, a : Int) -> Array[Int] {
  f.res[a]
}

// ---------------------------------------------------------------------------
// Standard presheaves.
// ---------------------------------------------------------------------------

///|
/// The constant presheaf with k sections (all restrictions the identity).
pub fn psh_constant(site : Site, k : Int) -> PSh {
  let fibers : Array[Int] = []
  let res : Array[Array[Int]] = []
  for _u = 0; _u < site.objs.length(); _u = _u + 1 {
    fibers.push(k)
  }
  for _a = 0; _a < site.arrows.length(); _a = _a + 1 {
    let row : Array[Int] = []
    for s = 0; s < k; s = s + 1 {
      row.push(s)
    }
    res.push(row)
  }
  psh(fibers, res)
}

///|
/// Sections = functions from the points of U to {0,...,k-1}, written in base k
/// (digit x = the value at the point x).  This is the sheaf of *locally
/// constant* functions, i.e. the sheafification of the constant presheaf.
pub fn locally_constant(site : Site, k : Int) -> PSh {
  let fibers : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    fibers.push(@tl.ipow(k, site.objs[u].length()))
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for s = 0; s < fibers[arr.cod]; s = s + 1 {
      // (s ∘ pmap)(x) = s(pmap[x])
      let mut t = 0
      let mut pow = 1
      for x = 0; x < arr.pmap.length(); x = x + 1 {
        let digit = s / @tl.ipow(k, arr.pmap[x]) % k
        t = t + digit * pow
        pow = pow * k
      }
      row.push(t)
    }
    res.push(row)
  }
  psh(fibers, res)
}

///|
/// A "connected components" presheaf attached to a subset `keep` of the
/// ambient points: F(U) = k^(number of connected components of U ∩ keep),
/// connectedness being measured in the incidence graph of the site's objects
/// (two points are adjacent when they lie in a common minimal open).  For
/// keep = everything this is the locally constant sheaf; for a proper open it
/// is a constructible sheaf, and T8 stratifies it.
pub fn components_presheaf(
  site : Site,
  k : Int,
  keep : Array[Int],
  adj : Array[Array[Int]]
) -> PSh {
  let fibers : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    fibers.push(@tl.ipow(k, ncomponents(site, u, keep, adj)))
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for s = 0; s < fibers[arr.cod]; s = s + 1 {
      row.push(restrict_components(site, k, keep, adj, a, s))
    }
    res.push(row)
  }
  psh(fibers, res)
}

///|
fn ncomponents(
  site : Site,
  u : Int,
  keep : Array[Int],
  adj : Array[Array[Int]]
) -> Int {
  let pts : Array[Int] = []
  for x in site.objs[u] {
    if in_list(keep, x) {
      pts.push(x)
    }
  }
  if pts.length() == 0 {
    return 0
  }
  // union-find along the adjacency restricted to pts
  let parent : Array[Int] = []
  for i = 0; i < site.objs[u].length(); i = i + 1 {
    parent.push(i)
  }
  for i = 0; i < pts.length(); i = i + 1 {
    for j = 0; j < pts.length(); j = j + 1 {
      if in_list(adj[pts[i]], pts[j]) {
        union(parent, index_in(site.objs[u], pts[i]), index_in(site.objs[u], pts[j]))
      }
    }
  }
  let mut n = 0
  for i = 0; i < pts.length(); i = i + 1 {
    if find(parent, index_in(site.objs[u], pts[i])) == index_in(site.objs[u], pts[i]) {
      n = n + 1
    }
  }
  n
}

///|
fn restrict_components(
  site : Site,
  k : Int,
  keep : Array[Int],
  adj : Array[Array[Int]],
  a : Int,
  s : Int
) -> Int {
  // a section of F(cod a) is a labelling of the components of
  // cod(a) ∩ keep; its restriction labels the components of dom(a) ∩ keep by
  // the label of the component that contains it.
  let cod = site.arrows[a].cod
  let dom = site.arrows[a].dom
  // component ids inside cod
  let cid_cod : Array[Int] = component_ids(site, cod, keep, adj)
  let cid_dom : Array[Int] = component_ids(site, dom, keep, adj)
  let pm = site.arrows[a].pmap
  // map each point of dom to the point of cod
  let mut out = 0
  let mut pow = 1
  // components of dom, in order of first appearance
  let seen : Array[Int] = []
  for i = 0; i < site.objs[dom].length(); i = i + 1 {
    let x = site.objs[dom][i]
    if !(in_list(keep, x)) {
      continue
    }
    let c = cid_dom[i]
    let mut dup = false
    for t = 0; t < seen.length(); t = t + 1 {
      if seen[t] == c {
        dup = true
        break
      }
    }
    if dup {
      continue
    }
    seen.push(c)
    // the label of the component of cod containing the image point
    let img = pm[i]
    let lab = s / @tl.ipow(k, cid_cod[img]) % k
    out = out + lab * pow
    pow = pow * k
  }
  out
}

///|
fn component_ids(
  site : Site,
  u : Int,
  keep : Array[Int],
  adj : Array[Array[Int]]
) -> Array[Int] {
  // component id per point of u (-1 if the point is not in keep)
  let ids : Array[Int] = []
  let parent : Array[Int] = []
  for i = 0; i < site.objs[u].length(); i = i + 1 {
    parent.push(i)
  }
  for i = 0; i < site.objs[u].length(); i = i + 1 {
    if in_list(keep, site.objs[u][i]) {
      for j = 0; j < site.objs[u].length(); j = j + 1 {
        if in_list(keep, site.objs[u][j]) &&
          in_list(adj[site.objs[u][i]], site.objs[u][j]) {
          union(parent, i, j)
        }
      }
    }
  }
  let rep : Array[Int] = []
  for i = 0; i < site.objs[u].length(); i = i + 1 {
    if !(in_list(keep, site.objs[u][i])) {
      ids.push(0 - 1)
    } else {
      let r = find(parent, i)
      let mut idx = 0
      let mut found = false
      for t = 0; t < rep.length(); t = t + 1 {
        if rep[t] == r {
          idx = t
          found = true
          break
        }
      }
      if !(found) {
        idx = rep.length()
        rep.push(r)
      }
      ids.push(idx)
    }
  }
  ids
}

///|
fn in_list(xs : Array[Int], x : Int) -> Bool {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return true
    }
  }
  false
}

///|
fn index_in(xs : Array[Int], x : Int) -> Int {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return i
    }
  }
  0 - 1
}

///|
fn find(parent : Array[Int], x : Int) -> Int {
  let mut r = x
  while parent[r] != r {
    r = parent[r]
  }
  r
}

///|
fn union(parent : Array[Int], a : Int, b : Int) -> Unit {
  let ra = find(parent, a)
  let rb = find(parent, b)
  if ra != rb {
    parent[ra] = rb
  }
}

///|
/// The representable presheaf h_x(U) = Hom(U, x).
pub fn psh_representable(site : Site, x : Int) -> PSh {
  let secs : Array[Array[Int]] = []
  let fibers : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let ax = arrows_from_to(site, u, x)
    secs.push(ax)
    fibers.push(ax.length())
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for s = 0; s < fibers[arr.cod]; s = s + 1 {
      // s : cod -> x becomes s ∘ a : dom -> x
      let comp = compose(site, secs[arr.cod][s], a)
      row.push(index_in(secs[arr.dom], comp))
    }
    res.push(row)
  }
  psh(fibers, res)
}

// ---------------------------------------------------------------------------
// The sheaf condition.
// ---------------------------------------------------------------------------

///|
fn tuples(radices : Array[Int]) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  let cur : Array[Int] = Array::make(radices.length(), 0)
  let mut total = 1
  for i = 0; i < radices.length(); i = i + 1 {
    total = total * radices[i]
  }
  for t = 0; t < total; t = t + 1 {
    let mut v = t
    for i = 0; i < radices.length(); i = i + 1 {
      cur[i] = v % radices[i]
      v = v / radices[i]
    }
    out.push(cur.copy())
  }
  out
}

///|
/// All matching families for the covering family `fam` of the object `u`:
/// tuples (s_i) with F(p1)(s_i) = F(p2)(s_j) on U_i ×_U U_j for every i, j.
pub fn matching(site : Site, f : PSh, fam : Array[Int]) -> Array[Array[Int]] {
  let radices : Array[Int] = []
  for i = 0; i < fam.length(); i = i + 1 {
    radices.push(f.fibers[site.arrows[fam[i]].dom])
  }
  let out : Array[Array[Int]] = []
  for cand in tuples(radices) {
    let mut ok = true
    for i = 0; i < fam.length() && ok; i = i + 1 {
      for j = 0; j < fam.length() && ok; j = j + 1 {
        let w = site.fib[fam[i]][fam[j]]
        if w < 0 {
          ok = false
          break
        }
        let q1 = site.p1[fam[i]][fam[j]]
        let q2 = site.p2[fam[i]][fam[j]]
        if f.res[q1][cand[i]] != f.res[q2][cand[j]] {
          ok = false
        }
      }
    }
    if ok {
      out.push(cand)
    }
  }
  out
}

///|
/// The sections of F(u) whose restriction to the family `fam` is `m`.
pub fn amalgamations(
  _site : Site,
  f : PSh,
  u : Int,
  fam : Array[Int],
  m : Array[Int]
) -> Array[Int] {
  let out : Array[Int] = []
  for s = 0; s < f.fibers[u]; s = s + 1 {
    let mut ok = true
    for i = 0; i < fam.length() && ok; i = i + 1 {
      if f.res[fam[i]][s] != m[i] {
        ok = false
      }
    }
    if ok {
      out.push(s)
    }
  }
  out
}

///|
/// F is separated: every matching family has *at most* one amalgamation.
pub fn is_separated(site : Site, f : PSh) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    for c = 0; c < site.covers[u].length(); c = c + 1 {
      for m in matching(site, f, site.covers[u][c]) {
        if amalgamations(site, f, u, site.covers[u][c], m).length() > 1 {
          return false
        }
      }
    }
  }
  true
}

///|
/// F is a sheaf: every matching family has *exactly* one amalgamation (†).
pub fn is_sheaf(site : Site, f : PSh) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    for c = 0; c < site.covers[u].length(); c = c + 1 {
      for m in matching(site, f, site.covers[u][c]) {
        if amalgamations(site, f, u, site.covers[u][c], m).length() != 1 {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// The plus construction and sheafification.
// ---------------------------------------------------------------------------

///|
/// Local data at u: pairs (cover index, matching family).
fn local_data(site : Site, f : PSh, u : Int) -> Array[(Int, Array[Int])] {
  let out : Array[(Int, Array[Int])] = []
  for c = 0; c < site.covers[u].length(); c = c + 1 {
    for m in matching(site, f, site.covers[u][c]) {
      out.push((c, m))
    }
  }
  out
}

///|
/// Index of a local datum, or -1.
fn datum_index(data : Array[(Int, Array[Int])], c : Int, m : Array[Int]) -> Int {
  for i = 0; i < data.length(); i = i + 1 {
    let (ci, mi) = data[i]
    if ci == c && pmap_eq(mi, m) {
      return i
    }
  }
  0 - 1
}

///|
/// Two local data agree after restriction to their common refinement: for
/// every pair of members (a of R, b of R'), the pullbacks to
/// dom(a) ×_u dom(b) are equal.
fn agree_on_refinement(
  site : Site,
  f : PSh,
  r : Array[Int],
  m : Array[Int],
  r2 : Array[Int],
  m2 : Array[Int]
) -> Bool {
  for i = 0; i < r.length(); i = i + 1 {
    for j = 0; j < r2.length(); j = j + 1 {
      let w = site.fib[r[i]][r2[j]]
      if w < 0 {
        return false
      }
      let q1 = site.p1[r[i]][r2[j]]
      let q2 = site.p2[r[i]][r2[j]]
      if f.res[q1][m[i]] != f.res[q2][m2[j]] {
        return false
      }
    }
  }
  true
}

///|
/// The equivalence classes (germs) of local data at u: the transitive closure
/// of "agree on the common refinement".
pub fn germ_classes(site : Site, f : PSh, u : Int) -> (Int, Array[Int]) {
  let data = local_data(site, f, u)
  let n = data.length()
  let parent : Array[Int] = []
  for i = 0; i < n; i = i + 1 {
    parent.push(i)
  }
  for i = 0; i < n; i = i + 1 {
    let (ci, mi) = data[i]
    for j = i + 1; j < n; j = j + 1 {
      let (cj, mj) = data[j]
      if agree_on_refinement(
        site, f, site.covers[u][ci], mi, site.covers[u][cj], mj,
      ) {
        union(parent, i, j)
      }
    }
  }
  // renumber the classes
  let reps : Array[Int] = []
  let cls : Array[Int] = Array::make(n, 0 - 1)
  for i = 0; i < n; i = i + 1 {
    let r = find(parent, i)
    let mut idx = 0 - 1
    for t = 0; t < reps.length(); t = t + 1 {
      if reps[t] == r {
        idx = t
        break
      }
    }
    if idx < 0 {
      idx = reps.length()
      reps.push(r)
    }
    cls[i] = idx
  }
  (reps.length(), cls)
}

///|
/// The plus construction F⁺ (see the header): F⁺(u) is the set of germs of
/// matching families at u, and restrictions are computed by base change.
pub fn plus(site : Site, f : PSh) -> PSh {
  // germs per object, with the local data they contain
  let nclass : Array[Int] = []
  let cls : Array[Array[Int]] = []
  let datas : Array[Array[(Int, Array[Int])]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let (nc, cl) = germ_classes(site, f, u)
    nclass.push(nc)
    cls.push(cl)
    datas.push(local_data(site, f, u))
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for g = 0; g < nclass[arr.cod]; g = g + 1 {
      // pick a representative local datum of the germ g
      let mut rep = 0 - 1
      for i = 0; i < cls[arr.cod].length(); i = i + 1 {
        if cls[arr.cod][i] == g {
          rep = i
          break
        }
      }
      let (ci, m) = datas[arr.cod][rep]
      row.push(pull_germ(site, f, cls, datas, a, site.covers[arr.cod][ci], m))
    }
    res.push(row)
  }
  psh(nclass, res)
}

///|
/// Restrict a germ along the arrow `a : v -> u`: base-change the cover, then
/// re-index by the covering basis of v.  Every choice of lift is checked to
/// give the same germ; if not, the site is not a pretopology.
fn pull_germ(
  site : Site,
  f : PSh,
  cls : Array[Array[Int]],
  datas : Array[Array[(Int, Array[Int])]],
  a : Int,
  cover : Array[Int],
  m : Array[Int]
) -> Int {
  let v = site.arrows[a].dom
  // base change: P_i = v ×_u dom(a_i), q1 : P_i -> v, q2 : P_i -> dom(a_i)
  let pobjs : Array[Int] = []
  let q1s : Array[Int] = []
  let q2s : Array[Int] = []
  for i = 0; i < cover.length(); i = i + 1 {
    let w = site.fib[a][cover[i]]
    if w < 0 {
      abort("plus: the site is not closed under base change")
    }
    pobjs.push(w)
    q1s.push(site.p1[a][cover[i]])
    q2s.push(site.p2[a][cover[i]])
  }
  if !(is_cover(site, v, q1s)) {
    abort("plus: base change of a cover is not a cover")
  }
  let mut best = 0 - 1
  for c = 0; c < site.covers[v].length(); c = c + 1 {
    let b = site.covers[v][c]
    let lifted = lift_to_basis(site, f, b, pobjs, q1s, q2s, m)
    let idx = datum_index(datas[v], c, lifted)
    if idx >= 0 {
      let g = cls[v][idx]
      if best < 0 {
        best = g
      } else if best != g {
        abort("plus: restriction depends on the choice of lift")
      }
    }
  }
  best
}

///|
/// Pull a matching family on the base-changed cover back to the covering basis
/// `b` of v: each member b_y : D_y -> v is lifted to some P_i.
fn lift_to_basis(
  site : Site,
  f : PSh,
  b : Array[Int],
  pobjs : Array[Int],
  q1s : Array[Int],
  q2s : Array[Int],
  m : Array[Int]
) -> Array[Int] {
  let out : Array[Int] = []
  for y = 0; y < b.length(); y = y + 1 {
    let by = b[y]
    let dy = site.arrows[by].dom
    let mut got = 0 - 1
    let mut i = 0
    while i < pobjs.length() && got < 0 {
      for l in arrows_from_to(site, dy, pobjs[i]) {
        if compose(site, q1s[i], l) == by {
          got = f.res[compose(site, q2s[i], l)][m[i]]
          break
        }
      }
      i = i + 1
    }
    if got < 0 {
      abort("plus: no lift of a basis member to the base-changed cover")
    }
    out.push(got)
  }
  out
}

///|
/// The sheafification F^# = F⁺⁺, together with nothing else (the unit is
/// `unit_map`).
pub fn sheafify(site : Site, f : PSh) -> PSh {
  plus(site, plus(site, f))
}

///|
/// The unit η_F : F -> F^# (as an array of maps F(u) -> F^#(u)).
pub fn unit_map(site : Site, f : PSh) -> Array[Array[Int]] {
  let f1 = plus(site, f)
  let f2 = plus(site, f1)
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let row : Array[Int] = []
    for s = 0; s < f.fibers[u]; s = s + 1 {
      // the germ at u of the datum (basis cover, restrictions of s)
      let c = 0
      let cov = site.covers[u][c]
      let m : Array[Int] = []
      for i = 0; i < cov.length(); i = i + 1 {
        m.push(f.res[cov[i]][s])
      }
      let d1 = local_data(site, f, u)
      let i1 = datum_index(d1, c, m)
      let g1 = germ_classes(site, f, u).1[i1]
      // now the same for F⁺
      let m2 : Array[Int] = []
      for i = 0; i < cov.length(); i = i + 1 {
        m2.push(f1.res[cov[i]][g1])
      }
      let d2 = local_data(site, f1, u)
      let i2 = datum_index(d2, c, m2)
      let g2 = germ_classes(site, f1, u).1[i2]
      if g2 < 0 || g2 >= f2.fibers[u] {
        abort("unit_map: germ out of range")
      }
      row.push(g2)
    }
    out.push(row)
  }
  out
}

// ---------------------------------------------------------------------------
// Morphisms of presheaves.
// ---------------------------------------------------------------------------

///|
pub(all) struct PMor {
  phi : Array[Array[Int]]
}

///|
pub fn pmor(phi : Array[Array[Int]]) -> PMor {
  { phi, }
}

///|
/// Naturality: G(a) ∘ φ_cod = φ_dom ∘ F(a) for every arrow a.
pub fn is_natural(site : Site, f : PSh, g : PSh, phi : Array[Array[Int]]) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    if phi[u].length() != f.fibers[u] {
      return false
    }
    for s = 0; s < f.fibers[u]; s = s + 1 {
      if phi[u][s] < 0 || phi[u][s] >= g.fibers[u] {
        return false
      }
    }
  }
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    for s = 0; s < f.fibers[arr.cod]; s = s + 1 {
      if g.res[a][phi[arr.cod][s]] != phi[arr.dom][f.res[a][s]] {
        return false
      }
    }
  }
  true
}

///|
/// The number of natural transformations F => G (exhaustive; only usable for
/// small presheaves).
///|
/// Every natural transformation F => G, by brute force over the (finite) set
/// of all families of maps.  Exponential in the fibre sizes: it is only meant
/// for the small sites of the test suite.
pub fn nat_morphisms(site : Site, f : PSh, g : PSh) -> Array[Array[Array[Int]]] {
  let radices : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    radices.push(@tl.ipow(g.fibers[u], f.fibers[u]))
  }
  let out : Array[Array[Array[Int]]] = []
  for t in tuples(radices) {
    let phi : Array[Array[Int]] = []
    for u = 0; u < site.objs.length(); u = u + 1 {
      let mut v = t[u]
      let row : Array[Int] = []
      for s = 0; s < f.fibers[u]; s = s + 1 {
        row.push(v % g.fibers[u])
        v = v / g.fibers[u]
      }
      phi.push(row)
    }
    if is_natural(site, f, g, phi) {
      out.push(phi)
    }
  }
  out
}

///|
/// The number of natural transformations F => G.
pub fn count_nat(site : Site, f : PSh, g : PSh) -> Int {
  nat_morphisms(site, f, g).length()
}

///|
/// Every component is a bijection.
pub fn is_iso(site : Site, f : PSh, g : PSh, phi : Array[Array[Int]]) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    if f.fibers[u] != g.fibers[u] {
      return false
    }
    let seen : Array[Int] = []
    for s = 0; s < f.fibers[u]; s = s + 1 {
      for t = 0; t < seen.length(); t = t + 1 {
        if seen[t] == phi[u][s] {
          return false
        }
      }
      seen.push(phi[u][s])
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Stalks.
// ---------------------------------------------------------------------------

///|
/// A pointed neighbourhood of the point x of u: an arrow a : v -> u together
/// with a point y of v mapping to x.
pub(all) struct Nbhd {
  obj : Int
  arr : Int
  pt : Int
}

///|
fn nbhds(site : Site, u : Int, x : Int) -> Array[Nbhd] {
  let out : Array[Nbhd] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    if site.arrows[a].cod != u {
      continue
    }
    for y = 0; y < site.arrows[a].pmap.length(); y = y + 1 {
      if site.arrows[a].pmap[y] == x {
        out.push({ obj: site.arrows[a].dom, arr: a, pt: y, })
      }
    }
  }
  out
}

///|
/// The stalk F_x = colim over the pointed neighbourhoods of x: elements are
/// germs (v, y, s) with s ∈ F(v), two such being identified when they agree
/// after pulling back to a common smaller neighbourhood.
pub fn stalk(site : Site, f : PSh, u : Int, x : Int) -> (Int, Array[Array[Int]]) {
  let nb = nbhds(site, u, x)
  // elements: (index of the neighbourhood, section)
  let elems : Array[(Int, Int)] = []
  for i = 0; i < nb.length(); i = i + 1 {
    for s = 0; s < f.fibers[nb[i].obj]; s = s + 1 {
      elems.push((i, s))
    }
  }
  let n = elems.length()
  let parent : Array[Int] = []
  for i = 0; i < n; i = i + 1 {
    parent.push(i)
  }
  for i = 0; i < n; i = i + 1 {
    let (ni, si) = elems[i]
    for j = i + 1; j < n; j = j + 1 {
      let (nj, sj) = elems[j]
      if germs_equal(site, f, nb[ni], si, nb[nj], sj) {
        union(parent, i, j)
      }
    }
  }
  let reps : Array[Int] = []
  let cls : Array[Int] = Array::make(n, 0 - 1)
  for i = 0; i < n; i = i + 1 {
    let r = find(parent, i)
    let mut idx = 0 - 1
    for t = 0; t < reps.length(); t = t + 1 {
      if reps[t] == r {
        idx = t
        break
      }
    }
    if idx < 0 {
      idx = reps.length()
      reps.push(r)
    }
    cls[i] = idx
  }
  // class of each element, grouped by neighbourhood
  let per : Array[Array[Int]] = []
  for i = 0; i < nb.length(); i = i + 1 {
    per.push([])
  }
  for i = 0; i < n; i = i + 1 {
    let (ni, si) = elems[i]
    while per[ni].length() <= si {
      per[ni].push(0 - 1)
    }
    per[ni][si] = cls[i]
  }
  (reps.length(), per)
}

///|
fn germs_equal(
  site : Site,
  f : PSh,
  p : Nbhd,
  s : Int,
  q : Nbhd,
  t : Int
) -> Bool {
  // a common refinement: w -> dom(p), w -> dom(q) over u, carrying a point
  // above pt(p) and pt(q)
  let arrp = site.arrows[p.arr]
  let arrq = site.arrows[q.arr]
  if arrp.cod != arrq.cod {
    return false
  }
  for w = 0; w < site.objs.length(); w = w + 1 {
    for h1 in arrows_from_to(site, w, p.obj) {
      for h2 in arrows_from_to(site, w, q.obj) {
        if !(pmap_eq(
          pmap_comp(arrp.pmap, site.arrows[h1].pmap),
          pmap_comp(arrq.pmap, site.arrows[h2].pmap),
        )) {
          continue
        }
        for z = 0; z < site.objs[w].length(); z = z + 1 {
          if site.arrows[h1].pmap[z] == p.pt &&
            site.arrows[h2].pmap[z] == q.pt {
            if f.res[h1][s] == f.res[h2][t] {
              return true
            }
          }
        }
      }
    }
  }
  false
}

///|
/// The germ map F(v) -> F_x for the neighbourhood (a : v -> u, y ↦ x).
pub fn germ_map(site : Site, f : PSh, u : Int, x : Int, v : Int, a : Int, y : Int) -> Array[Int] {
  let (_n, per) = stalk(site, f, u, x)
  let nb = nbhds(site, u, x)
  for i = 0; i < nb.length(); i = i + 1 {
    if nb[i].obj == v && nb[i].arr == a && nb[i].pt == y {
      return per[i]
    }
  }
  abort("germ_map: not a neighbourhood")
}

///|
/// The map of stalks F_x -> G_x induced by a morphism φ : F => G.
pub fn stalk_map(
  site : Site,
  f : PSh,
  g : PSh,
  phi : Array[Array[Int]],
  u : Int,
  x : Int
) -> Array[Int] {
  let (nf, per) = stalk(site, f, u, x)
  let (ng, per_g) = stalk(site, g, u, x)
  let nb = nbhds(site, u, x)
  let out : Array[Int] = Array::make(nf, 0 - 1)
  for i = 0; i < nb.length(); i = i + 1 {
    for s = 0; s < f.fibers[nb[i].obj]; s = s + 1 {
      let gf = per[i][s]
      let gg = per_g[i][phi[nb[i].obj][s]]
      if out[gf] >= 0 && out[gf] != gg {
        abort("stalk_map: not well defined")
      }
      out[gf] = gg
    }
  }
  for i = 0; i < nf; i = i + 1 {
    if out[i] < 0 || out[i] >= ng {
      abort("stalk_map: undefined germ")
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Products (needed for left exactness) and the Cech complex.
// ---------------------------------------------------------------------------

///|
/// The product presheaf (F × G)(U) = F(U) × G(U).
pub fn psh_product(site : Site, f : PSh, g : PSh) -> PSh {
  let fibers : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    fibers.push(f.fibers[u] * g.fibers[u])
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for s = 0; s < fibers[arr.cod]; s = s + 1 {
      let sf = s / g.fibers[arr.cod]
      let sg = s % g.fibers[arr.cod]
      row.push(f.res[a][sf] * g.fibers[arr.dom] + g.res[a][sg])
    }
    res.push(row)
  }
  psh(fibers, res)
}

///|
/// The projections F × G -> F and F × G -> G.
pub fn product_proj(
  site : Site,
  f : PSh,
  g : PSh
) -> (Array[Array[Int]], Array[Array[Int]]) {
  let pf : Array[Array[Int]] = []
  let pg : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let rf : Array[Int] = []
    let rg : Array[Int] = []
    for s = 0; s < f.fibers[u] * g.fibers[u]; s = s + 1 {
      rf.push(s / g.fibers[u])
      rg.push(s % g.fibers[u])
    }
    pf.push(rf)
    pg.push(rg)
  }
  (pf, pg)
}

///|
/// The (n+1)-fold intersections of the covering family that are non-empty:
/// the n-simplices of the Cech nerve, listed as increasing index tuples.
pub fn cech_simplices(site : Site, fam : Array[Int], n : Int) -> Array[Array[Int]] {
  let k = fam.length()
  let out : Array[Array[Int]] = []
  for mask = 0; mask < @tl.ipow(2, k); mask = mask + 1 {
    let mut cnt = 0
    for i = 0; i < k; i = i + 1 {
      if mask / @tl.ipow(2, i) % 2 == 1 {
        cnt = cnt + 1
      }
    }
    if cnt != n + 1 {
      continue
    }
    let idx : Array[Int] = []
    let arrs : Array[Int] = []
    for i = 0; i < k; i = i + 1 {
      if mask / @tl.ipow(2, i) % 2 == 1 {
        idx.push(i)
        arrs.push(fam[i])
      }
    }
    let (w, _p) = multi_fib(site, arrs)
    if w >= 0 && site.objs[w].length() > 0 {
      out.push(idx)
    }
  }
  out
}

///|
/// The simplicial coboundary δ^n : C^n -> C^{n+1} of the Cech nerve of `fam`
/// (rows indexed by (n+1)-simplices, columns by n-simplices).
pub fn cech_coboundary(
  site : Site,
  fam : Array[Int],
  n : Int
) -> Array[Array[Int]] {
  let top = cech_simplices(site, fam, n + 1)
  let bot = cech_simplices(site, fam, n)
  let out : Array[Array[Int]] = []
  for t in top {
    let row : Array[Int] = []
    for s in bot {
      // is s obtained from t by deleting the k-th entry?
      let mut val = 0
      let mut k = 0
      while k < t.length() {
        let mut ok = true
        let mut pos = 0
        for i = 0; i < t.length() && ok; i = i + 1 {
          if i == k {
            continue
          }
          if pos >= s.length() || s[pos] != t[i] {
            ok = false
          }
          pos = pos + 1
        }
        if ok {
          val = if k % 2 == 0 { 1 } else { 0 - 1 }
        }
        k = k + 1
      }
      row.push(val)
    }
    out.push(row)
  }
  out
}

///|
/// The rank of an integer matrix modulo `m` (m prime): the number of Smith
/// invariant factors not divisible by m.
pub fn rank_mod(mat : Array[Array[Int]], m : Int) -> Int {
  if mat.length() == 0 || mat[0].length() == 0 {
    return 0
  }
  let d = @nf.snf_diag(@nf.smith_normal_form(mat))
  let mut r = 0
  for i = 0; i < d.length(); i = i + 1 {
    if d[i] % m != 0 {
      r = r + 1
    }
  }
  r
}

///|
/// dim_{F_m} H^n of the Cech nerve of the cover `fam` (m prime):
/// dim H^n = |N_n| - rank_m δ^{n-1} - rank_m δ^n.
pub fn cech_betti(site : Site, fam : Array[Int], m : Int, n : Int) -> Int {
  let kn = cech_simplices(site, fam, n).length()
  let rp = if n == 0 { 0 } else { rank_mod(cech_coboundary(site, fam, n - 1), m) }
  let rn = rank_mod(cech_coboundary(site, fam, n), m)
  kn - rp - rn
}

///|
/// The integral Cech complex, as a chain complex (degrees reversed), so that
/// `@derived.homology` returns H^{N-n} in degree n.
pub fn cech_cx(site : Site, fam : Array[Int]) -> @derived.Cx {
  let mut top = 0
  while cech_simplices(site, fam, top).length() > 0 && top < 8 {
    top = top + 1
  }
  top = top - 1
  if top < 0 {
    return @derived.cx_zero([0])
  }
  let ranks : Array[Int] = []
  let ds : Array[Array[Array[Int]]] = []
  let mut n = top
  while n >= 0 {
    ranks.push(cech_simplices(site, fam, n).length())
    n = n - 1
  }
  // d[n] : C_n -> C_{n-1} with C_n = C^{top-n}
  // d[n] : C_n -> C_{n-1} with C_n = C^{top-n}, so d[n] = delta^{top-n}
  let mut n2 = top
  while n2 >= 0 {
    ds.push(cech_coboundary(site, fam, n2))
    n2 = n2 - 1
  }
  @derived.cx_new(ranks, ds)
}

///|
/// The Cech cohomology groups H^0, H^1, ... of the cover: the Cech complex is
/// a cochain complex, and `cech_cx` re-indexes it as a chain complex with
/// C_n = C^{top-n}, so H_n of that chain complex is H^{top-n}.  This reverses
/// the list back into the cohomological order.
pub fn cech_cohomology(
  site : Site,
  fam : Array[Int]
) -> Array[Array[Array[Int]]] {
  let cx = cech_cx(site, fam)
  let h = @derived.homology(cx)
  let out : Array[Array[Array[Int]]] = []
  let mut i = h.length() - 1
  while i >= 0 {
    out.push(h[i])
    i = i - 1
  }
  out
}

// ---------------------------------------------------------------------------
// Stratification: the stalk type stratifies the space, and a sheaf is a local
// system on each stratum.
// ---------------------------------------------------------------------------

///|
/// The index of the minimal open neighbourhood of the ambient point x, or -1.
pub fn min_open_obj(site : Site, x : Int) -> Int {
  let mut best = 0 - 1
  for u = 0; u < site.objs.length(); u = u + 1 {
    if !(in_list(site.objs[u], x)) {
      continue
    }
    if best < 0 || site.objs[u].length() < site.objs[best].length() {
      best = u
    }
  }
  best
}

///|
/// The transition map F(↑x) -> F(↑y) for comparable points (y ∈ ↑x), i.e. the
/// map induced on stalks by the specialisation x ≤ y.
pub fn transition(site : Site, f : PSh, x : Int, y : Int) -> Array[Int] {
  let mx = min_open_obj(site, x)
  let my = min_open_obj(site, y)
  if mx < 0 || my < 0 {
    abort("transition: point not in the site")
  }
  // is ↑y ⊆ ↑x ?
  for p in site.objs[my] {
    if !(in_list(site.objs[mx], p)) {
      abort("transition: points are not comparable this way")
    }
  }
  let pm : Array[Int] = []
  for p in site.objs[my] {
    pm.push(index_in(site.objs[mx], p))
  }
  let a = arrow_find(site.arrows, my, mx, pm)
  if a < 0 {
    abort("transition: no arrow between the minimal opens")
  }
  f.res[a]
}

///|
/// Is the transition F(↑x) -> F(↑y) a bijection?  (Equivalently: the sheaf is
/// locally constant along the specialisation x ≤ y.)
pub fn transition_iso(site : Site, f : PSh, x : Int, y : Int) -> Bool {
  let t = transition(site, f, x, y)
  if t.length() != f.fibers[min_open_obj(site, y)] {
    return false
  }
  let seen : Array[Int] = []
  for v in t {
    for s = 0; s < seen.length(); s = s + 1 {
      if seen[s] == v {
        return false
      }
    }
    seen.push(v)
  }
  true
}

///|
/// Is the stalk transition between two comparable points a bijection, in
/// whichever direction the specialisation goes?  (`transition` is directed:
/// it is the map F_x => F_y induced by x <= y, i.e. by ↑y ⊆ ↑x.)
pub fn transition_iso_undirected(site : Site, f : PSh, x : Int, y : Int) -> Bool {
  let mx = min_open_obj(site, x)
  let my = min_open_obj(site, y)
  let mut y_below_x = true
  for p in site.objs[my] {
    if !(in_list(site.objs[mx], p)) {
      y_below_x = false
    }
  }
  if y_below_x {
    transition_iso(site, f, x, y)
  } else {
    transition_iso(site, f, y, x)
  }
}

///|
/// The stratification of the space by the local system structure of F: two
/// points are in the same stratum when they can be joined by a chain of
/// comparable points along which all transition maps are bijections.
pub fn strata(site : Site, f : PSh, npts : Int) -> Array[Array[Int]] {
  let parent : Array[Int] = []
  for x = 0; x < npts; x = x + 1 {
    parent.push(x)
  }
  for x = 0; x < npts; x = x + 1 {
    for y = 0; y < npts; y = y + 1 {
      if x == y {
        continue
      }
      if comparable(site, x, y) && transition_iso_undirected(site, f, x, y) {
        union(parent, x, y)
      }
    }
  }
  let reps : Array[Int] = []
  let out : Array[Array[Int]] = []
  for x = 0; x < npts; x = x + 1 {
    let r = find(parent, x)
    let mut idx = 0 - 1
    for t = 0; t < reps.length(); t = t + 1 {
      if reps[t] == r {
        idx = t
        break
      }
    }
    if idx < 0 {
      idx = reps.length()
      reps.push(r)
      out.push([x])
    } else {
      out[idx].push(x)
    }
  }
  out
}

///|
/// Are x and y comparable in the specialisation order (↑y ⊆ ↑x or ↑x ⊆ ↑y)?
pub fn comparable(site : Site, x : Int, y : Int) -> Bool {
  let mx = min_open_obj(site, x)
  let my = min_open_obj(site, y)
  if mx < 0 || my < 0 {
    return false
  }
  let mut sub = true
  for p in site.objs[my] {
    if !(in_list(site.objs[mx], p)) {
      sub = false
    }
  }
  if sub {
    return true
  }
  for p in site.objs[mx] {
    if !(in_list(site.objs[my], p)) {
      return false
    }
  }
  true
}

///|
/// The cocycle condition for the local system on a stratum: for x ≤ z ≤ y
/// inside the stratum, σ_{xy} = σ_{zy} ∘ σ_{xz}.
pub fn cocycle_ok(site : Site, f : PSh, x : Int, z : Int, y : Int) -> Bool {
  let xz = transition(site, f, x, z)
  let zy = transition(site, f, z, y)
  let xy = transition(site, f, x, y)
  for s = 0; s < xy.length(); s = s + 1 {
    if xy[s] != zy[xz[s]] {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Germs via a minimal neighbourhood (fast path).
//
// In both sites every point x of an object u has a *smallest* neighbourhood:
// the point inclusion Spec F_p -> u (Nisnevich site) and the minimal open ↑x
// (finite space site).  A smallest neighbourhood is final in the system of
// neighbourhoods, so the colimit degenerates:
//
//        F_x = F(V_x)      and      s ↦ s|_{V_x}   is the germ map.
//
// The general colimit is implemented by `stalk` above; the test
// "T5 stalks..." checks that the two agree where the general one is
// affordable.
// ---------------------------------------------------------------------------

///|
/// The smallest neighbourhood of the point x of u: (its object, the arrow to
/// u, the point of that object above x).
pub fn min_nbhd(site : Site, u : Int, x : Int) -> (Int, Int, Int) {
  let mut best = (0 - 1, 0 - 1, 0 - 1)
  for a = 0; a < site.arrows.length(); a = a + 1 {
    if site.arrows[a].cod != u {
      continue
    }
    let v = site.arrows[a].dom
    for y = 0; y < site.arrows[a].pmap.length(); y = y + 1 {
      if site.arrows[a].pmap[y] != x {
        continue
      }
      let (b0, b1, _b2) = best
      if b1 < 0 || site.objs[v].length() < site.objs[b0].length() {
        best = (v, a, y)
      }
    }
  }
  let (b0, b1, b2) = best
  if b1 < 0 {
    abort("min_nbhd: the point has no neighbourhood")
  }
  (b0, b1, b2)
}

///|
/// The germ family of every section: `germ_family(F, u)[s][x]` is the germ of
/// the section s at the point x, an element of F(V_x).
pub fn germ_family(site : Site, f : PSh, u : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  let nb : Array[Int] = []
  for x = 0; x < site.objs[u].length(); x = x + 1 {
    let (_v, a, _y) = min_nbhd(site, u, x)
    nb.push(a)
  }
  for s = 0; s < f.fibers[u]; s = s + 1 {
    let row : Array[Int] = []
    for x = 0; x < nb.length(); x = x + 1 {
      row.push(f.res[nb[x]][s])
    }
    out.push(row)
  }
  out
}

///|
/// The stalk F_x = F(V_x) (as a set of that many germs).
pub fn stalk_at(site : Site, f : PSh, u : Int, x : Int) -> Int {
  let (v, _a, _y) = min_nbhd(site, u, x)
  f.fibers[v]
}

///|
/// The map of stalks induced by a morphism at the point x of u.
pub fn stalk_map_at(
  site : Site,
  f : PSh,
  g : PSh,
  phi : Array[Array[Int]],
  u : Int,
  x : Int
) -> Array[Int] {
  let (v, _a, _y) = min_nbhd(site, u, x)
  if phi[v].length() != f.fibers[v] {
    abort("stalk_map_at: wrong shape")
  }
  for i = 0; i < phi[v].length(); i = i + 1 {
    if phi[v][i] < 0 || phi[v][i] >= g.fibers[v] {
      abort("stalk_map_at: out of range")
    }
  }
  phi[v]
}

///|
/// Germs determine sections of a separated presheaf (in particular of a
/// sheaf): the germ family map is injective.
pub fn germ_injective(site : Site, f : PSh) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    let gf = germ_family(site, f, u)
    for i = 0; i < gf.length(); i = i + 1 {
      for j = i + 1; j < gf.length(); j = j + 1 {
        if pmap_eq(gf[i], gf[j]) {
          return false
        }
      }
    }
  }
  true
}

///|
/// The inverse of a bijection given as an array (aborts if it is not one).
fn invert(tab : Array[Int], n : Int) -> Array[Int] {
  let out : Array[Int] = Array::make(n, 0 - 1)
  for i = 0; i < tab.length(); i = i + 1 {
    if tab[i] < 0 || tab[i] >= n || out[tab[i]] >= 0 {
      abort("invert: not a bijection")
    }
    out[tab[i]] = i
  }
  out
}

///|
/// The map F^# => G^# induced by a morphism φ : F => G: on germs it is the
/// stalk map of φ, and a sheaf is determined by its germs, so this defines the
/// unique natural transformation with η_G ∘ φ = φ^# ∘ η_F.
pub fn sheafify_map(
  site : Site,
  f : PSh,
  g : PSh,
  phi : Array[Array[Int]]
) -> Array[Array[Int]] {
  let f2 = sheafify(site, f)
  let g2 = sheafify(site, g)
  let ef = unit_map(site, f)
  let eg = unit_map(site, g)
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let gf_f = germ_family(site, f2, u)
    let gf_g = germ_family(site, g2, u)
    let row : Array[Int] = []
    for s = 0; s < f2.fibers[u]; s = s + 1 {
      let target : Array[Int] = []
      for x = 0; x < site.objs[u].length(); x = x + 1 {
        let (v, _a, _y) = min_nbhd(site, u, x)
        let back = invert(ef[v], f2.fibers[v])
        let s_x = back[gf_f[s][x]]
        let t_x = phi[v][s_x]
        target.push(eg[v][t_x])
      }
      // the unique section of G^#(u) with these germs
      let mut found = 0 - 1
      for t = 0; t < g2.fibers[u]; t = t + 1 {
        if pmap_eq(gf_g[t], target) {
          found = t
          break
        }
      }
      if found < 0 {
        abort("sheafify_map: no section with the prescribed germs")
      }
      row.push(found)
    }
    out.push(row)
  }
  out
}

// ---------------------------------------------------------------------------
// Two running examples of finite sites.
// ---------------------------------------------------------------------------

///|
/// The upper sets of the poset generated by `above` (points are 0..n-1 and
/// `above[x]` lists the points above x), i.e. the open sets of the finite
/// (Alexandrov) space of the poset, in increasing binary order.
fn opens_of(above : Array[Array[Int]]) -> Array[Array[Int]] {
  let n = above.length()
  let out : Array[Array[Int]] = []
  for mask = 0; mask < @tl.ipow(2, n); mask = mask + 1 {
    let u : Array[Int] = []
    for i = 0; i < n; i = i + 1 {
      if mask / @tl.ipow(2, i) % 2 == 1 {
        u.push(i)
      }
    }
    let mut ok = true
    for p in u {
      for q in above[p] {
        if !(in_list(u, q)) {
          ok = false
        }
      }
    }
    if ok {
      out.push(u)
    }
  }
  out
}

///|
/// The finite model of the interval: points 0, 1 the vertices and 2 the edge
/// (0 <= 2, 1 <= 2).  It has 5 opens and is contractible.
pub fn interval_opens() -> Array[Array[Int]] {
  opens_of([[2], [2], []])
}

///|
/// The finite model of the circle: points 0, 1, 2 the vertices and
/// 3 = e01, 4 = e12, 5 = e02 the edges.  It has 18 opens, and McCord's
/// theorem identifies its cohomology with the cohomology of S^1 (which the
/// Cech computation in the test suite confirms: b = (1, 1, 0)).
pub fn triangle_opens() -> Array[Array[Int]] {
  opens_of([[3, 5], [3, 4], [4, 5], [], [], []])
}

///|
/// The adjacency of the points of a space: two points are neighbours when
/// they are comparable in the specialisation order, i.e. when they lie in a
/// common minimal open.  It is the "connectedness" relation used by
/// `components_presheaf`.
pub fn adjacency(site : Site, npts : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  for x = 0; x < npts; x = x + 1 {
    let row : Array[Int] = [x]
    for y = 0; y < npts; y = y + 1 {
      if y != x && comparable(site, x, y) {
        row.push(y)
      }
    }
    out.push(row)
  }
  out
}
