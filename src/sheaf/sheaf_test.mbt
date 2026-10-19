// ---------------------------------------------------------------------------
// Tests for the sheaf layer.  Each test is a theorem; see THEOREMS.md.
//
//   T1  F^+ is separated and F^# = (F^+)^+ is a sheaf (both sites)
//   T2  (constant k)^#  =  locally constant sheaf k
//   T3  η_F : F => F^# is an isomorphism iff F is a sheaf;  # is idempotent
//   T4  sheafification |= inclusion:  Nat(F^#, G) = Nat(F, G) for sheaves G
//   T5  stalks: F_x = F^#_x ; isos of sheaves are detected on stalks
//   T6  left exactness:  (F x G)^# = F^# x G^#
//   T7  Cech cohomology of the nerve  (= H^n of the space)
//   T8  stratification by the stalk, and the local system on each stratum
// ---------------------------------------------------------------------------

///|
fn mem(x : Int, xs : Array[Int]) -> Bool {
  for i = 0; i < xs.length(); i = i + 1 {
    if xs[i] == x {
      return true
    }
  }
  false
}

///|
fn digits(s : Int, k : Int, n : Int) -> Array[Int] {
  let out : Array[Int] = []
  let mut t = s
  for i = 0; i < n; i = i + 1 {
    out.push(t % k)
    t = t / k
  }
  out
}

///|
fn undigits(ds : Array[Int], k : Int) -> Int {
  let mut acc = 0
  for i = 0; i < ds.length(); i = i + 1 {
    acc = acc + ds[i] * @tl.ipow(k, i)
  }
  acc
}

///|
fn show(xs : Array[Int]) -> String {
  let mut s = "["
  for i = 0; i < xs.length(); i = i + 1 {
    if i > 0 {
      s = s + ","
    }
    s = s + xs[i].to_string()
  }
  s + "]"
}

// ---------------------------------------------------------------------------
// T1
// ---------------------------------------------------------------------------

///|
test "T1 @sheaf.plus separates and double @sheaf.plus sheaves" {
  let nis = @sheaf.nis_split_site(3)
  let iv = @sheaf.finite_space_site(3, @sheaf.interval_opens())
  // battery: (site, presheaf)
  let cases : Array[(@sheaf.Site, @sheaf.PSh)] = [
    (nis, @sheaf.psh_constant(nis, 2)),
    (nis, @sheaf.psh_constant(nis, 3)),
    (nis, @sheaf.locally_constant(nis, 2)),
    (nis, @sheaf.psh_representable(nis, 2)),
    (iv, @sheaf.psh_constant(iv, 2)),
    (iv, @sheaf.psh_constant(iv, 3)),
    (iv, @sheaf.locally_constant(iv, 2)),
    (iv, @sheaf.psh_representable(iv, 2)),
  ]
  for i = 0; i < cases.length(); i = i + 1 {
    let (site, f) = cases[i]
    assert_eq(@sheaf.psh_ok(site, f), true)
    let f1 = @sheaf.plus(site, f)
    let f2 = @sheaf.plus(site, f1)
    assert_eq(@sheaf.psh_ok(site, f1), true)
    assert_eq(@sheaf.psh_ok(site, f2), true)
    // F^+ is always separated
    assert_eq(@sheaf.is_separated(site, f1), true)
    // F^# = (F^+)^+ is always a sheaf
    assert_eq(@sheaf.is_sheaf(site, f2), true)
    // a sheaf is separated, i.e. determined by its germs
    assert_eq(@sheaf.germ_injective(site, f2), true)
    // # is idempotent up to equality of the fibre sizes
    let f3 = @sheaf.plus(site, @sheaf.plus(site, f2))
    assert_eq(show(f3.fibers), show(f2.fibers))
  }
}

// ---------------------------------------------------------------------------
// T2
// ---------------------------------------------------------------------------

///|
/// The number of digits of a section of a presheaf of k-valued functions.
fn ndigits(n : Int, k : Int) -> Int {
  let mut c = 0
  let mut t = n
  while t > 1 {
    t = t / k
    c = c + 1
  }
  c
}

///|
/// The constant section map F = constant(k) => G, for any presheaf G of
/// k-valued functions on the points (or the components) of the objects: the
/// section i goes to the function which is constant equal to i.
fn const_sections(
  site : @sheaf.Site,
  g : @sheaf.PSh,
  k : Int
) -> Array[Array[Int]] {
  let f = @sheaf.psh_constant(site, k)
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let n = ndigits(g.fibers[u], k)
    let row : Array[Int] = []
    for s = 0; s < f.fibers[u]; s = s + 1 {
      let ds : Array[Int] = []
      for i = 0; i < n; i = i + 1 {
        ds.push(s)
      }
      row.push(undigits(ds, k))
    }
    out.push(row)
  }
  out
}

///|
/// (constant k)^# = the sheaf of locally constant k-valued functions.
fn check_t2(site : @sheaf.Site, lc : @sheaf.PSh, k : Int) -> Unit raise {
  let f = @sheaf.psh_constant(site, k)
  let f2 = @sheaf.sheafify(site, f)
  assert_eq(show(f2.fibers), show(lc.fibers))
  let alpha = const_sections(site, lc, k)
  assert_eq(@sheaf.is_natural(site, f, lc, alpha), true)
  // the universal property turns it into the isomorphism F^# => lc
  let psi = @sheaf.sheafify_map(site, f, lc, alpha)
  assert_eq(@sheaf.is_natural(site, f2, lc, psi), true)
  assert_eq(@sheaf.is_iso(site, f2, lc, psi), true)
  // the unit F => F^# is not an isomorphism: F is not a sheaf
  assert_eq(@sheaf.is_sheaf(site, f), false)
  assert_eq(@sheaf.is_iso(site, f, f2, @sheaf.unit_map(site, f)), false)
}

///|
test "T2 sheafification of the constant presheaf is the locally constant sheaf" {
  // on the Nisnevich site every object is a disjoint union of points, so the
  // locally constant sheaf is the sheaf of all functions to k
  let nis = @sheaf.nis_split_site(3)
  check_t2(nis, @sheaf.locally_constant(nis, 2), 2)
  // on a topological space it is the sheaf of functions constant on the
  // connected components, which is what `components_presheaf` builds
  let iv = @sheaf.finite_space_site(3, @sheaf.interval_opens())
  let cf = @sheaf.components_presheaf(iv, 2, [0, 1, 2], @sheaf.adjacency(iv, 3))
  assert_eq(@sheaf.psh_ok(iv, cf), true)
  check_t2(iv, cf, 2)
}

// ---------------------------------------------------------------------------
// T3
// ---------------------------------------------------------------------------

///|
/// A presheaf on the interval which is *not* separated: two distinct sections
/// of the whole space restrict to the same section of every member of the
/// cover.  (F(u) = k for the top and the two stars, all restrictions out of
/// the top being constant.)
fn non_separated(site : @sheaf.Site) -> @sheaf.PSh {
  let mut top = 0
  for u = 0; u < site.objs.length(); u = u + 1 {
    if site.objs[u].length() > site.objs[top].length() {
      top = u
    }
  }
  let fibers : Array[Int] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    fibers.push(if site.objs[u].length() >= 2 { 2 } else { 1 })
  }
  let res : Array[Array[Int]] = []
  for a = 0; a < site.arrows.length(); a = a + 1 {
    let arr = site.arrows[a]
    let row : Array[Int] = []
    for s = 0; s < fibers[arr.cod]; s = s + 1 {
      if arr.dom == arr.cod {
        row.push(s)
      } else if fibers[arr.dom] == 1 {
        row.push(0)
      } else if arr.cod == top {
        row.push(0)
      } else {
        row.push(s)
      }
    }
    res.push(row)
  }
  @sheaf.psh(fibers, res)
}

///|
test "T3 eta is an isomorphism exactly for sheaves, and # is idempotent" {
  let nis = @sheaf.nis_split_site(3)
  let iv = @sheaf.finite_space_site(3, @sheaf.interval_opens())
  // sheaves: the unit is an isomorphism
  let sheaves : Array[(@sheaf.Site, @sheaf.PSh)] = [
    (nis, @sheaf.locally_constant(nis, 2)),
    (nis, @sheaf.psh_representable(nis, 2)),
    (iv, @sheaf.locally_constant(iv, 2)),
  ]
  for i = 0; i < sheaves.length(); i = i + 1 {
    let (site, f) = sheaves[i]
    assert_eq(@sheaf.is_sheaf(site, f), true)
    assert_eq(@sheaf.is_natural(site, f, @sheaf.sheafify(site, f), @sheaf.unit_map(site, f)), true)
    assert_eq(@sheaf.is_iso(site, f, @sheaf.sheafify(site, f), @sheaf.unit_map(site, f)), true)
  }
  // non-sheaves: the unit is not an isomorphism
  let not_sheaves : Array[(@sheaf.Site, @sheaf.PSh)] = [
    (nis, @sheaf.psh_constant(nis, 2)),
    (iv, @sheaf.psh_constant(iv, 2)),
  ]
  for i = 0; i < not_sheaves.length(); i = i + 1 {
    let (site, f) = not_sheaves[i]
    assert_eq(@sheaf.is_sheaf(site, f), false)
    assert_eq(@sheaf.is_iso(site, f, @sheaf.sheafify(site, f), @sheaf.unit_map(site, f)), false)
  }
  // the non separated presheaf: F^+ identifies the two sections of the top
  let site = iv
  let g = non_separated(site)
  assert_eq(@sheaf.psh_ok(site, g), true)
  assert_eq(@sheaf.is_separated(site, g), false)
  assert_eq(@sheaf.germ_injective(site, g), false)
  let g1 = @sheaf.plus(site, g)
  let g2 = @sheaf.plus(site, g1)
  assert_eq(@sheaf.is_sheaf(site, g2), true)
  let mut top = 0
  for u = 0; u < site.objs.length(); u = u + 1 {
    if site.objs[u].length() > site.objs[top].length() {
      top = u
    }
  }
  assert_eq(g.fibers[top], 2)
  // the two sections agree on the cover, so the unit identifies them ...
  let eta = @sheaf.unit_map(site, g)
  assert_eq(eta[top][0], eta[top][1])
  // ... and the sheafification adds the local data that was missing:
  // F^#(top) is the set of locally constant k-valued functions on the top
  assert_eq(g2.fibers[top], 4)
}

// ---------------------------------------------------------------------------
// T4
// ---------------------------------------------------------------------------

///|
test "T4 sheafification is left adjoint to the inclusion of sheaves" {
  // the site is small enough to enumerate every natural transformation
  let nis = @sheaf.nis_split_site(2)
  let lc = @sheaf.locally_constant(nis, 2)
  let f = @sheaf.psh_constant(nis, 2)
  let f2 = @sheaf.sheafify(nis, f)
  let eta = @sheaf.unit_map(nis, f)
  assert_eq(@sheaf.is_sheaf(nis, lc), true)
  // Nat(F^#, G) -> Nat(F, G), φ |-> φ ∘ η, is a bijection
  let big = @sheaf.nat_morphisms(nis, f2, lc)
  let small = @sheaf.nat_morphisms(nis, f, lc)
  assert_eq(big.length(), small.length())
  for i = 0; i < big.length(); i = i + 1 {
    assert_eq(index_of_nat(nis, small, compose_nat(nis, big[i], eta)), true)
  }
  for j = 0; j < small.length(); j = j + 1 {
    let mut found = 0
    for i = 0; i < big.length(); i = i + 1 {
      if nat_eq(nis, compose_nat(nis, big[i], eta), small[j]) {
        found = found + 1
      }
    }
    assert_eq(found, 1)
  }
  // the same on the bigger site, constructively: every α : F => G with G a
  // sheaf extends uniquely to α^# : F^# => G with α^# ∘ η = α
  let nis3 = @sheaf.nis_split_site(3)
  let lc3 = @sheaf.locally_constant(nis3, 2)
  let f3 = @sheaf.psh_constant(nis3, 2)
  let f3s = @sheaf.sheafify(nis3, f3)
  let eta3 = @sheaf.unit_map(nis3, f3)
  let alpha = const_sections(nis3, lc3, 2)
  assert_eq(@sheaf.is_natural(nis3, f3, lc3, alpha), true)
  let psi = @sheaf.sheafify_map(nis3, f3, lc3, alpha)
  assert_eq(@sheaf.is_natural(nis3, f3s, lc3, psi), true)
  let mut ok = true
  for u = 0; u < nis3.objs.length(); u = u + 1 {
    for s = 0; s < f3.fibers[u]; s = s + 1 {
      if psi[u][eta3[u][s]] != alpha[u][s] {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
}

///|
/// (φ ∘ η)[u][s] = φ[u][η[u][s]]
fn compose_nat(
  site : @sheaf.Site,
  phi : Array[Array[Int]],
  eta : Array[Array[Int]]
) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let row : Array[Int] = []
    for s = 0; s < eta[u].length(); s = s + 1 {
      row.push(phi[u][eta[u][s]])
    }
    out.push(row)
  }
  out
}

///|
fn nat_eq(
  site : @sheaf.Site,
  a : Array[Array[Int]],
  b : Array[Array[Int]]
) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    if a[u].length() != b[u].length() {
      return false
    }
    for s = 0; s < a[u].length(); s = s + 1 {
      if a[u][s] != b[u][s] {
        return false
      }
    }
  }
  true
}

///|
fn index_of_nat(
  site : @sheaf.Site,
  xs : Array[Array[Array[Int]]],
  a : Array[Array[Int]]
) -> Bool {
  for i = 0; i < xs.length(); i = i + 1 {
    if nat_eq(site, xs[i], a) {
      return true
    }
  }
  false
}

// ---------------------------------------------------------------------------
// T5
// ---------------------------------------------------------------------------

///|
/// The morphism of locally constant sheaves induced by a map of digits:
/// a section is a string of digits in base k, send it to the same string read
/// in base l (which requires l >= k for it to be a well defined section).
fn reencode(site : @sheaf.Site, k : Int, l : Int) -> Array[Array[Int]] {
  let f = @sheaf.locally_constant(site, k)
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let row : Array[Int] = []
    for s = 0; s < f.fibers[u]; s = s + 1 {
      let ds = digits(s, k, site.objs[u].length())
      row.push(undigits(ds, l))
    }
    out.push(row)
  }
  out
}

///|
/// The "digit reduction" map: read a base-k string modulo l.
fn fold_digits(site : @sheaf.Site, k : Int, l : Int) -> Array[Array[Int]] {
  let f = @sheaf.locally_constant(site, k)
  let out : Array[Array[Int]] = []
  for u = 0; u < site.objs.length(); u = u + 1 {
    let row : Array[Int] = []
    for s = 0; s < f.fibers[u]; s = s + 1 {
      let ds = digits(s, k, site.objs[u].length())
      let red : Array[Int] = []
      for i = 0; i < ds.length(); i = i + 1 {
        red.push(ds[i] % l)
      }
      row.push(undigits(red, l))
    }
    out.push(row)
  }
  out
}

///|
test "T5 stalks are preserved by sheafification and detect isomorphisms" {
  let nis = @sheaf.nis_split_site(3)
  let fs : Array[@sheaf.PSh] = [
    @sheaf.psh_constant(nis, 2),
    @sheaf.psh_constant(nis, 3),
    @sheaf.locally_constant(nis, 2),
  ]
  for i = 0; i < fs.length(); i = i + 1 {
    let f = fs[i]
    let f2 = @sheaf.sheafify(nis, f)
    let eta = @sheaf.unit_map(nis, f)
    // F_x = F^#_x for every point of every object
    for u = 0; u < nis.objs.length(); u = u + 1 {
      for x = 0; x < nis.objs[u].length(); x = x + 1 {
        assert_eq(@sheaf.stalk_at(nis, f2, u, x), @sheaf.stalk_at(nis, f, u, x))
        let sm = @sheaf.stalk_map_at(nis, f, f2, eta, u, x)
        assert_eq(is_bijection(sm, f2.fibers[@sheaf.min_nbhd(nis, u, x).0]), true)
      }
    }
  }
  // a morphism of sheaves is an isomorphism iff it is one on every stalk
  let lc2 = @sheaf.locally_constant(nis, 2)
  let lc3 = @sheaf.locally_constant(nis, 3)
  // (a) the inclusion of digits 2 -> 3: injective on stalks, not surjective
  let inc = reencode(nis, 2, 3)
  assert_eq(@sheaf.is_natural(nis, lc2, lc3, inc), true)
  assert_eq(@sheaf.is_iso(nis, lc2, lc3, inc), false)
  assert_eq(all_stalks_bijective(nis, lc2, lc3, inc), false)
  assert_eq(all_stalks_injective(nis, lc2, lc3, inc), true)
  // (b) reduction modulo 2: surjective on stalks, not injective
  let fold = fold_digits(nis, 3, 2)
  assert_eq(@sheaf.is_natural(nis, lc3, lc2, fold), true)
  assert_eq(@sheaf.is_iso(nis, lc3, lc2, fold), false)
  assert_eq(all_stalks_bijective(nis, lc3, lc2, fold), false)
  // (c) the identity is an isomorphism, stalkwise and globally
  let idm = reencode(nis, 2, 2)
  assert_eq(@sheaf.is_natural(nis, lc2, lc2, idm), true)
  assert_eq(@sheaf.is_iso(nis, lc2, lc2, idm), true)
  assert_eq(all_stalks_bijective(nis, lc2, lc2, idm), true)
}

///|
fn is_bijection(tab : Array[Int], n : Int) -> Bool {
  if tab.length() != n {
    return false
  }
  let seen : Array[Int] = []
  for i = 0; i < tab.length(); i = i + 1 {
    if tab[i] < 0 || tab[i] >= n {
      return false
    }
    for j = 0; j < seen.length(); j = j + 1 {
      if seen[j] == tab[i] {
        return false
      }
    }
    seen.push(tab[i])
  }
  true
}

///|
fn all_stalks_bijective(
  site : @sheaf.Site,
  f : @sheaf.PSh,
  g : @sheaf.PSh,
  phi : Array[Array[Int]]
) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    for x = 0; x < site.objs[u].length(); x = x + 1 {
      let sm = @sheaf.stalk_map_at(site, f, g, phi, u, x)
      if !(is_bijection(sm, g.fibers[@sheaf.min_nbhd(site, u, x).0])) {
        return false
      }
    }
  }
  true
}

///|
fn all_stalks_injective(
  site : @sheaf.Site,
  f : @sheaf.PSh,
  g : @sheaf.PSh,
  phi : Array[Array[Int]]
) -> Bool {
  for u = 0; u < site.objs.length(); u = u + 1 {
    for x = 0; x < site.objs[u].length(); x = x + 1 {
      let sm = @sheaf.stalk_map_at(site, f, g, phi, u, x)
      let mut ok = true
      for i = 0; i < sm.length(); i = i + 1 {
        for j = i + 1; j < sm.length(); j = j + 1 {
          if sm[i] == sm[j] {
            ok = false
          }
        }
      }
      if !ok {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// T6
// ---------------------------------------------------------------------------

///|
test "T6 sheafification preserves finite products" {
  let nis = @sheaf.nis_split_site(3)
  let pairs : Array[(@sheaf.PSh, @sheaf.PSh)] = [
    (@sheaf.psh_constant(nis, 2), @sheaf.psh_constant(nis, 3)),
    (@sheaf.psh_constant(nis, 2), @sheaf.locally_constant(nis, 2)),
  ]
  for i = 0; i < pairs.length(); i = i + 1 {
    let (f, g) = pairs[i]
    let fg = @sheaf.psh_product(nis, f, g)
    let f2 = @sheaf.sheafify(nis, f)
    let g2 = @sheaf.sheafify(nis, g)
    let fg2 = @sheaf.sheafify(nis, fg)
    let f2g2 = @sheaf.psh_product(nis, f2, g2)
    // the canonical map (F x G)^# => F^# x G^# is the product of the
    // sheafified projections
    let (pf, pg) = @sheaf.product_proj(nis, f, g)
    let pf2 = @sheaf.sheafify_map(nis, fg, f, pf)
    let pg2 = @sheaf.sheafify_map(nis, fg, g, pg)
    let psi : Array[Array[Int]] = []
    for u = 0; u < nis.objs.length(); u = u + 1 {
      let row : Array[Int] = []
      for s = 0; s < fg2.fibers[u]; s = s + 1 {
        row.push(pf2[u][s] * g2.fibers[u] + pg2[u][s])
      }
      psi.push(row)
    }
    assert_eq(@sheaf.is_natural(nis, fg2, f2g2, psi), true)
    assert_eq(@sheaf.is_iso(nis, fg2, f2g2, psi), true)
    // (F x G)^# and F^# x G^# have the same fibres
    assert_eq(show(fg2.fibers), show(f2g2.fibers))
  }
}

// ---------------------------------------------------------------------------
// T7
// ---------------------------------------------------------------------------

///|
test "T7 Cech cohomology is the cohomology of the space" {
  // the circle: nerve of the three stars has 6 vertices, 9 edges, 3 triangles
  let cir = @sheaf.finite_space_site(6, @sheaf.triangle_opens())
  let mut top = 0
  for u = 0; u < cir.objs.length(); u = u + 1 {
    if cir.objs[u].length() > cir.objs[top].length() {
      top = u
    }
  }
  let fam = cir.covers[top][0]
  assert_eq(cir.objs.length(), 18)
  assert_eq(@sheaf.cech_simplices(cir, fam, 0).length(), 6)
  assert_eq(@sheaf.cech_simplices(cir, fam, 1).length(), 9)
  assert_eq(@sheaf.cech_simplices(cir, fam, 2).length(), 3)
  assert_eq(@sheaf.cech_simplices(cir, fam, 3).length(), 0)
  // Euler characteristic of the nerve = 6 - 9 + 3 = 0 = chi(S^1)
  let chi = 6 - 9 + 3
  assert_eq(chi, 0)
  // Betti numbers mod m: (1, 1, 0) for the circle
  let ms = [2, 3]
  for i = 0; i < ms.length(); i = i + 1 {
    let m = ms[i]
    assert_eq(@sheaf.cech_betti(cir, fam, m, 0), 1)
    assert_eq(@sheaf.cech_betti(cir, fam, m, 1), 1)
    assert_eq(@sheaf.cech_betti(cir, fam, m, 2), 0)
  }
  // integral cohomology through the derived package: H^0 = Z, H^1 = Z, H^2 = 0
  let h = @sheaf.cech_cohomology(cir, fam)
  assert_eq(@derived.grp_rank(h[0]), 1)
  assert_eq(@derived.grp_rank(h[1]), 1)
  assert_eq(@derived.grp_rank(h[2]), 0)
  // H^1(S^1) = Z is torsion free
  assert_eq(@derived.grp_factors(h[1]).length(), 0)
  // the interval: contractible, so (1, 0, 0)
  let iv = @sheaf.finite_space_site(3, @sheaf.interval_opens())
  let fam2 = iv.covers[4][0]
  assert_eq(@sheaf.cech_simplices(iv, fam2, 0).length(), 3)
  assert_eq(@sheaf.cech_simplices(iv, fam2, 1).length(), 3)
  assert_eq(@sheaf.cech_simplices(iv, fam2, 2).length(), 1)
  for i = 0; i < ms.length(); i = i + 1 {
    let m = ms[i]
    assert_eq(@sheaf.cech_betti(iv, fam2, m, 0), 1)
    assert_eq(@sheaf.cech_betti(iv, fam2, m, 1), 0)
  }
  let h2 = @sheaf.cech_cohomology(iv, fam2)
  assert_eq(@derived.grp_rank(h2[0]), 1)
  assert_eq(@derived.grp_rank(h2[1]), 0)
  assert_eq(@derived.grp_rank(h2[2]), 0)
}

// ---------------------------------------------------------------------------
// T8
// ---------------------------------------------------------------------------

///|
///|
/// x <= y in the specialisation order of a finite space (<= x is in the
/// closure of y, i.e. the minimal open of y is contained in the one of x).
fn leq(site : @sheaf.Site, x : Int, y : Int) -> Bool {
  let mx = @sheaf.min_open_obj(site, x)
  let my = @sheaf.min_open_obj(site, y)
  for p in site.objs[my] {
    if !(mem(p, site.objs[mx])) {
      return false
    }
  }
  true
}

///|
test "T8 @sheaf.strata of a constructible sheaf and the local system on a stratum" {
  let cir = @sheaf.finite_space_site(6, @sheaf.triangle_opens())
  let adj = @sheaf.adjacency(cir, 6)
  // the locally constant sheaf of rank 2: one stratum, every transition iso
  let lc = @sheaf.components_presheaf(cir, 2, [0, 1, 2, 3, 4, 5], adj)
  assert_eq(@sheaf.psh_ok(cir, lc), true)
  assert_eq(@sheaf.is_sheaf(cir, lc), true)
  let s0 = @sheaf.strata(cir, lc, 6)
  assert_eq(s0.length(), 1)
  assert_eq(s0[0].length(), 6)
  // the constructible sheaf F(V) = k^{#pi_0(V \ {2})}: the big stratum plus
  // the point that was removed
  let keep : Array[Int] = [0, 1, 3, 4, 5]
  let f = @sheaf.components_presheaf(cir, 2, keep, adj)
  assert_eq(@sheaf.psh_ok(cir, f), true)
  assert_eq(@sheaf.is_sheaf(cir, f), true)
  let st = @sheaf.strata(cir, f, 6)
  assert_eq(st.length(), 2)
  let sizes : Array[Int] = []
  for i = 0; i < st.length(); i = i + 1 {
    sizes.push(st[i].length())
  }
  sizes.sort()
  assert_eq(show(sizes), "[1,5]")
  // the stalk is k on the big stratum and k^2 above the missing point
  assert_eq(f.fibers[@sheaf.min_open_obj(cir, 0)], 2)
  assert_eq(f.fibers[@sheaf.min_open_obj(cir, 2)], 4)
  // inside a stratum all transitions are bijections and satisfy the cocycle
  // condition σ_{xy} = σ_{zy} ∘ σ_{xz} for x <= z <= y
  for i = 0; i < st.length(); i = i + 1 {
    for x in st[i] {
      for y in st[i] {
        if x == y || !(leq(cir, x, y)) {
          continue
        }
        assert_eq(@sheaf.transition_iso(cir, f, x, y), true)
        for z in st[i] {
          if leq(cir, x, z) && leq(cir, z, y) {
            assert_eq(@sheaf.cocycle_ok(cir, f, x, z, y), true)
          }
        }
      }
    }
  }
  // across the strata the transition is not a bijection: 2 -> 4
  assert_eq(@sheaf.transition_iso(cir, f, 2, 4), false)
}
