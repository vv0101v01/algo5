// ---------------------------------------------------------------------------
// 層化 (sheafification), part 1: finite sites.
//
// A *site* is a small category equipped with a Grothendieck topology.  We keep
// everything finite and concrete: an object is a finite set of points, a
// morphism is a map of point sets (so composition is composition of maps), the
// topology is given by a *basis* of covering families, and fibre products are
// found by their universal property (searched for, and verified, exhaustively).
//
// Two sites are constructed:
//
//   * `nis_split_site(n)` — the small Nisnevich site of Spec F_p, restricted to
//     the totally split etale algebras A = F_p x ... x F_p (a finite set of n
//     or fewer points).  Morphisms and covers are certified by `src/nis`.
//
//   * `finite_space_site(npts, opens)` — the site of open sets of a finite
//     topological space, with the basis of minimal open neighbourhoods.  Taking
//     the finite model of S^1 gives a site with genuinely non-trivial Cech
//     cohomology.
// ---------------------------------------------------------------------------

///|
/// A morphism `dom -> cod` of the site, given by its action on points.
pub(all) struct Arrow {
  dom : Int
  cod : Int
  pmap : Array[Int]
}

///|
/// A finite site: objects, morphisms, composition, a basis of covering
/// families, and a choice of fibre products (with their projections).
pub(all) struct Site {
  objs : Array[Array[Int]]
  arrows : Array[Arrow]
  comp : Array[Array[Int]]
  covers : Array[Array[Array[Int]]]
  fib : Array[Array[Int]]
  p1 : Array[Array[Int]]
  p2 : Array[Array[Int]]
}

///|
pub fn arrow(dom : Int, cod : Int, pmap : Array[Int]) -> Arrow {
  { dom, cod, pmap, }
}

///|
fn pmap_eq(a : Array[Int], b : Array[Int]) -> Bool {
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

///|
/// The composite of two point maps: first `b`, then `a`.
fn pmap_comp(a : Array[Int], b : Array[Int]) -> Array[Int] {
  let out : Array[Int] = []
  for x = 0; x < b.length(); x = x + 1 {
    out.push(a[b[x]])
  }
  out
}

///|
/// Index of the arrow `dom -> cod` with the given point map, or -1.
pub fn arrow_find(
  arrows : Array[Arrow],
  dom : Int,
  cod : Int,
  pmap : Array[Int]
) -> Int {
  for i = 0; i < arrows.length(); i = i + 1 {
    if arrows[i].dom == dom && arrows[i].cod == cod &&
      pmap_eq(arrows[i].pmap, pmap) {
      return i
    }
  }
  0 - 1
}

///|
/// All arrows `dom -> cod`.
pub fn arrows_from_to(
  site : Site,
  dom : Int,
  cod : Int
) -> Array[Int] {
  let out : Array[Int] = []
  for i = 0; i < site.arrows.length(); i = i + 1 {
    if site.arrows[i].dom == dom && site.arrows[i].cod == cod {
      out.push(i)
    }
  }
  out
}

///|
/// The identity arrow of an object.
pub fn id_arrow(site : Site, u : Int) -> Int {
  let pm : Array[Int] = []
  for x = 0; x < site.objs[u].length(); x = x + 1 {
    pm.push(x)
  }
  arrow_find(site.arrows, u, u, pm)
}

///|
/// The composite `a ∘ b` (apply `b` first), or -1 if not composable.
pub fn compose(site : Site, a : Int, b : Int) -> Int {
  if site.arrows[b].cod != site.arrows[a].dom {
    return 0 - 1
  }
  site.comp[a][b]
}

///|
fn compatible_pairs(site : Site, a : Int, b : Int) -> Int {
  if site.arrows[a].cod != site.arrows[b].cod {
    return 0 - 1
  }
  let mut n = 0
  for x = 0; x < site.objs[site.arrows[a].dom].length(); x = x + 1 {
    for y = 0; y < site.objs[site.arrows[b].dom].length(); y = y + 1 {
      if site.arrows[a].pmap[x] == site.arrows[b].pmap[y] {
        n = n + 1
      }
    }
  }
  n
}

///|
/// The fibre product `dom(a) ×_cod dom(b)`, found by the universal property:
/// an object `w` with arrows `q1 : w -> dom(a)`, `q2 : w -> dom(b)`,
/// `a ∘ q1 = b ∘ q2`, such that `z ↦ (q1(z), q2(z))` is a *bijection* from the
/// points of `w` onto the set of compatible pairs.  (Both sites below are
/// concrete, so this is exactly the usual fibre product of sets/open sets.)
fn fibre_product_of(site : Site, a : Int, b : Int) -> (Int, Int, Int) {
  let np = compatible_pairs(site, a, b)
  if np < 0 {
    return (0 - 1, 0 - 1, 0 - 1)
  }
  let da = site.arrows[a].dom
  let db = site.arrows[b].dom
  for w = 0; w < site.objs.length(); w = w + 1 {
    if site.objs[w].length() != np {
      continue
    }
    let cands1 = arrows_from_to(site, w, da)
    let cands2 = arrows_from_to(site, w, db)
    for i1 = 0; i1 < cands1.length(); i1 = i1 + 1 {
      let q1 = cands1[i1]
      for i2 = 0; i2 < cands2.length(); i2 = i2 + 1 {
        let q2 = cands2[i2]
        // a ∘ q1 = b ∘ q2
        let lhs = pmap_comp(site.arrows[a].pmap, site.arrows[q1].pmap)
        let rhs = pmap_comp(site.arrows[b].pmap, site.arrows[q2].pmap)
        if !(pmap_eq(lhs, rhs)) {
          continue
        }
        // the induced map to the set of pairs is a bijection
        let seen : Array[Int] = []
        let mut ok = true
        for z = 0; z < site.objs[w].length() && ok; z = z + 1 {
          let key = site.arrows[q1].pmap[z] *
            site.objs[db].length() +
            site.arrows[q2].pmap[z]
          for s = 0; s < seen.length(); s = s + 1 {
            if seen[s] == key {
              ok = false
              break
            }
          }
          seen.push(key)
        }
        if ok {
          return (w, q1, q2)
        }
      }
    }
  }
  (0 - 1, 0 - 1, 0 - 1)
}

///|
/// Assemble a site: fill in the composition table and every fibre product.
pub fn site_new(
  objs : Array[Array[Int]],
  arrows : Array[Arrow],
  covers : Array[Array[Array[Int]]]
) -> Site {
  let partial = {
    objs,
    arrows,
    comp: [],
    covers,
    fib: [],
    p1: [],
    p2: [],
  }
  let n = arrows.length()
  let comp : Array[Array[Int]] = []
  for a = 0; a < n; a = a + 1 {
    let row : Array[Int] = []
    for b = 0; b < n; b = b + 1 {
      if arrows[b].cod != arrows[a].dom {
        row.push(0 - 1)
      } else {
        row.push(
          arrow_find(
            arrows,
            arrows[b].dom,
            arrows[a].cod,
            pmap_comp(arrows[a].pmap, arrows[b].pmap),
          ),
        )
      }
    }
    comp.push(row)
  }
  let fib : Array[Array[Int]] = []
  let p1 : Array[Array[Int]] = []
  let p2 : Array[Array[Int]] = []
  for a = 0; a < n; a = a + 1 {
    let r0 : Array[Int] = []
    let r1 : Array[Int] = []
    let r2 : Array[Int] = []
    for b = 0; b < n; b = b + 1 {
      let (w, q1, q2) = fibre_product_of(partial, a, b)
      r0.push(w)
      r1.push(q1)
      r2.push(q2)
    }
    fib.push(r0)
    p1.push(r1)
    p2.push(r2)
  }
  { objs, arrows, comp, covers, fib, p1, p2, }
}

///|
/// Does the family `{a_i : U_i -> u}` cover `u`?  (Jointly surjective on
/// points; the empty family covers exactly the empty object.)
pub fn is_cover(site : Site, u : Int, fam : Array[Int]) -> Bool {
  for i = 0; i < fam.length(); i = i + 1 {
    if site.arrows[fam[i]].cod != u {
      return false
    }
  }
  let hit : Array[Int] = Array::make(site.objs[u].length(), 0)
  for i = 0; i < fam.length(); i = i + 1 {
    let a = fam[i]
    for x = 0; x < site.arrows[a].pmap.length(); x = x + 1 {
      hit[site.arrows[a].pmap[x]] = 1
    }
  }
  for x = 0; x < hit.length(); x = x + 1 {
    if hit[x] == 0 {
      return false
    }
  }
  true
}

///|
/// Site axioms, verified exhaustively: identities exist and act as such,
/// composition is closed, every listed family is a cover, and every pair of
/// arrows with a common codomain has a fibre product.
pub fn site_ok(site : Site) -> Bool {
  let n = site.arrows.length()
  for u = 0; u < site.objs.length(); u = u + 1 {
    let e = id_arrow(site, u)
    if e < 0 {
      return false
    }
    for a = 0; a < n; a = a + 1 {
      if site.arrows[a].dom == u && compose(site, a, e) != a {
        return false
      }
      if site.arrows[a].cod == u && compose(site, e, a) != a {
        return false
      }
    }
    for c = 0; c < site.covers[u].length(); c = c + 1 {
      if !(is_cover(site, u, site.covers[u][c])) {
        return false
      }
    }
  }
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n && site.arrows[a].cod == site.arrows[b].cod; b = b + 1 {
      if site.fib[a][b] < 0 {
        return false
      }
      // the projections really commute
      let left = compose(site, a, site.p1[a][b])
      let right = compose(site, b, site.p2[a][b])
      if left < 0 || left != right {
        return false
      }
    }
  }
  true
}

///|
/// The n-fold fibre product of a family of arrows with a common codomain:
/// returns (the object, the projections onto each factor).
pub fn multi_fib(site : Site, arrs : Array[Int]) -> (Int, Array[Int]) {
  if arrs.length() == 0 {
    abort("multi_fib: empty family")
  }
  if arrs.length() == 1 {
    return (site.arrows[arrs[0]].dom, [id_arrow(site, site.arrows[arrs[0]].dom)])
  }
  // fold: (((a0 × a1) × a2) × ...)
  let mut obj = site.fib[arrs[0]][arrs[1]]
  let mut projs : Array[Int] = [site.p1[arrs[0]][arrs[1]], site.p2[arrs[0]][arrs[1]]]
  let mut k = 2
  while k < arrs.length() {
    // the arrow from the current product to the common codomain
    let to_cod = compose(site, arrs[0], projs[0])
    let cur : Array[Int] = [to_cod]
    let nobj = site.fib[cur[0]][arrs[k]]
    let q1 = site.p1[cur[0]][arrs[k]]
    let q2 = site.p2[cur[0]][arrs[k]]
    let nprojs : Array[Int] = []
    for i = 0; i < projs.length(); i = i + 1 {
      nprojs.push(compose(site, projs[i], q1))
    }
    nprojs.push(q2)
    obj = nobj
    projs = nprojs
    k = k + 1
  }
  (obj, projs)
}

///|
/// The Cech face map `U_{i_0} × ... × U_{i_n} -> U_{i_0} × ... ĥ ... × U_{i_n}`
/// (drop the i-th factor): the unique arrow whose composites with the
/// projections of the target are the corresponding projections of the source.
pub fn face_map(site : Site, arrs : Array[Int], i : Int) -> Int {
  let (src, psrc) = multi_fib(site, arrs)
  let rest : Array[Int] = []
  for j = 0; j < arrs.length(); j = j + 1 {
    if j != i {
      rest.push(arrs[j])
    }
  }
  let (tgt, ptgt) = multi_fib(site, rest)
  let cands = arrows_from_to(site, src, tgt)
  for c = 0; c < cands.length(); c = c + 1 {
    let f = cands[c]
    let mut ok = true
    for j = 0; j < ptgt.length() && ok; j = j + 1 {
      if compose(site, ptgt[j], f) != psrc[j] {
        ok = false
      }
    }
    if ok {
      return f
    }
  }
  0 - 1
}

// ---------------------------------------------------------------------------
// Site 1: the small Nisnevich site of Spec F_p, restricted to the totally
// split etale algebras (finite sets of at most `nmax` points).
// ---------------------------------------------------------------------------

///|
fn split_et(k : Int) -> @nis.Et {
  let out : @nis.Et = []
  for i = 0; i < k; i = i + 1 {
    out.push(1)
  }
  out
}

///|
fn decode_base(t : Int, base : Int, len : Int) -> Array[Int] {
  let out : Array[Int] = []
  let mut v = t
  for i = 0; i < len; i = i + 1 {
    out.push(v % base)
    v = v / base
  }
  out
}

///|
/// The Nisnevich site on `Spec F_p, ..., Spec F_p^nmax` (empty scheme
/// included).  The covering basis of `u` is the family of all point inclusions
/// `Spec F_p -> u`; the empty family covers the empty scheme.
pub fn nis_split_site(nmax : Int) -> Site {
  let objs : Array[Array[Int]] = []
  for k = 0; k <= nmax; k = k + 1 {
    objs.push(init_range(k))
  }
  let arrows : Array[Arrow] = []
  let ets : Array[@nis.Et] = []
  for k = 0; k <= nmax; k = k + 1 {
    ets.push(split_et(k))
  }
  for dom = 0; dom <= nmax; dom = dom + 1 {
    for cod = 0; cod <= nmax; cod = cod + 1 {
      let total = @tl.ipow(cod, dom)
      for t = 0; t < total; t = t + 1 {
        let pm = decode_base(t, cod, dom)
        // certified by src/nis: every map between totally split algebras is a
        // morphism of F_p-algebras
        if @nis.is_mor(ets[cod], ets[dom], @nis.etmor_new(pm)) {
          arrows.push(arrow(dom, cod, pm))
        } else {
          abort("nis_split_site: not a morphism")
        }
      }
    }
  }
  // covering basis
  let covers : Array[Array[Array[Int]]] = []
  for k = 0; k <= nmax; k = k + 1 {
    let fam : Array[Int] = []
    for x = 0; x < k; x = x + 1 {
      let a = arrow_find(arrows, 1, k, [x])
      if a < 0 {
        abort("nis_split_site: missing point inclusion")
      }
      fam.push(a)
    }
    let one : Array[Array[Int]] = [fam]
    covers.push(one)
  }
  site_new(objs, arrows, covers)
}

///|
fn init_range(k : Int) -> Array[Int] {
  let out : Array[Int] = []
  for i = 0; i < k; i = i + 1 {
    out.push(i)
  }
  out
}

// ---------------------------------------------------------------------------
// Site 2: the site of open sets of a finite topological space.
// ---------------------------------------------------------------------------

///|
fn contains(xs : Array[Int], x : Int) -> Bool {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return true
    }
  }
  false
}

///|
fn index_of(xs : Array[Int], x : Int) -> Int {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return i
    }
  }
  0 - 1
}

///|
/// The smallest open containing `x` (the intersection of all of them).
pub fn minimal_open(opens : Array[Array[Int]], x : Int) -> Array[Int] {
  let mut best : Array[Int] = []
  for i = 0; i < opens.length(); i = i + 1 {
    if contains(opens[i], x) {
      if best.length() == 0 || opens[i].length() < best.length() {
        best = opens[i]
      }
    }
  }
  best
}

///|
pub fn open_index(opens : Array[Array[Int]], u : Array[Int]) -> Int {
  for i = 0; i < opens.length(); i = i + 1 {
    if opens[i].length() == u.length() {
      let mut ok = true
      for j = 0; j < u.length() && ok; j = j + 1 {
        if !contains(opens[i], u[j]) {
          ok = false
        }
      }
      if ok {
        return i
      }
    }
  }
  0 - 1
}

///|
/// The site of open sets of the finite space whose open sets are `opens`
/// (each a list of point labels).  Arrows are inclusions; the covering basis
/// of `u` is the family of minimal open neighbourhoods of the points of `u`.
pub fn finite_space_site(npts : Int, opens : Array[Array[Int]]) -> Site {
  let objs : Array[Array[Int]] = []
  for i = 0; i < opens.length(); i = i + 1 {
    objs.push(opens[i])
  }
  let arrows : Array[Arrow] = []
  for i = 0; i < objs.length(); i = i + 1 {
    for j = 0; j < objs.length(); j = j + 1 {
      // an arrow i -> j exists for every inclusion objs[i] ⊆ objs[j]
      let mut ok = true
      let pm : Array[Int] = []
      for x = 0; x < objs[i].length() && ok; x = x + 1 {
        let k = index_of(objs[j], objs[i][x])
        if k < 0 {
          ok = false
        } else {
          pm.push(k)
        }
      }
      if ok {
        arrows.push(arrow(i, j, pm))
      }
    }
  }
  let covers : Array[Array[Array[Int]]] = []
  for i = 0; i < objs.length(); i = i + 1 {
    let fam : Array[Int] = []
    let mins : Array[Int] = []
    for x = 0; x < objs[i].length(); x = x + 1 {
      let mo = minimal_open(opens, objs[i][x])
      let k = open_index(opens, mo)
      if k < 0 {
        abort("finite_space_site: minimal open missing")
      }
      let mut dup = false
      for s = 0; s < mins.length(); s = s + 1 {
        if mins[s] == k {
          dup = true
          break
        }
      }
      if !dup {
        mins.push(k)
      }
    }
    for s = 0; s < mins.length(); s = s + 1 {
      let a = arrow_find(arrows, mins[s], i, inclusion_pmap(objs, mins[s], i))
      if a < 0 {
        abort("finite_space_site: missing inclusion")
      }
      fam.push(a)
    }
    covers.push([[fam][0]])
  }
  let _ = npts
  site_new(objs, arrows, covers)
}

///|
fn inclusion_pmap(objs : Array[Array[Int]], sub : Int, sup : Int) -> Array[Int] {
  let pm : Array[Int] = []
  for x = 0; x < objs[sub].length(); x = x + 1 {
    pm.push(index_of(objs[sup], objs[sub][x]))
  }
  pm
}
