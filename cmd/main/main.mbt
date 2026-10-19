///|
/// 同構即相同 — a tour of `teichlab`.
///
/// Every line printed below is produced by the certified algorithms of the
/// library and is cross-checked by the test suite (`moon test`).
fn show_triples(ts : Array[(Int32, Int32, Int32)]) -> String {
  let mut out = "["
  for i = 0; i < ts.length(); i = i + 1 {
    let (a, b, c) = ts[i]
    if i > 0 {
      out = out + ", "
    }
    out = out + "(\{a},\{b},\{c})"
  }
  out + "]"
}

///|
fn show_roots(rs : Array[(Double, Int32)]) -> String {
  let mut out = "["
  for i = 0; i < rs.length(); i = i + 1 {
    let (w, m) = rs[i]
    if i > 0 {
      out = out + ", "
    }
    out = out + "(\{w}, mult \{m})"
  }
  out + "]"
}

///|
fn show_ints(xs : Array[Int32]) -> String {
  let mut out = "["
  for i = 0; i < xs.length(); i = i + 1 {
    if i > 0 {
      out = out + ", "
    }
    out = out + "\{xs[i]}"
  }
  out + "]"
}

///|
fn main {
  println("================================================================")
  println("  teichlab — 同構即相同 (isomorphism is identity)")
  println("  MoonBit · 零成本抽象 · 70 machine-checked theorems/tests")
  println("================================================================\n")

  // ---- 0. 零成本抽象: type-level naturals folded to a constant ----------
  let seven : @tl.NatV[@tl.Plus[@tl.N3, @tl.N4]] = @tl.reflect()
  println(
    "[tl]    type-level 3 + 4 reified at zero cost         = \{@tl.unwrap_nat(seven)}",
  )

  // ---- 1. 序 (order): Birkhoff and hook length -------------------------
  let pairs : Array[(Int32, Int32)] = [(0, 1), (0, 2), (2, 3), (2, 4)]
  let p = @order.poset_from_pairs(5, pairs)
  let le = @order.count_linear_extensions(p)
  let hl = @order.hook_length_forest(p)
  println(
    "[order] e(P) by exhaustive count / by hook length       = \{le} / \{hl}",
  )

  // ---- 2. 規範形式 (normal form): Smith and Groebner -------------------
  let m = [[2, 4, 4], [0 - 6, 6, 12], [10, 0 - 4, 0 - 16]]
  let s = @nf.smith_normal_form(m)
  println(
    "[nf]    Smith normal form of a 3x3 matrix              = \{show_ints(@nf.snf_diag(s))}",
  )
  println(
    "[nf]    cokernel: \{@nf.coker_rank(m)} free generator(s), torsion \{show_ints(@nf.invariant_factors(m))}",
  )

  // ---- 3. 路徑空間 (path space): pi_1 of a graph -----------------------
  let g : @path.Graph = { nv: 2, edges: [(0, 1), (0, 1), (0, 1)], }
  let fg = @path.fundamental_group(g, 0)
  println("[path]  pi_1(theta graph) = F_r with r                 = \{fg.0}")
  println(
    "[path]  F_2 ball of radius 3                           = \{@path.free_group_ball_size(2, 3)} elements",
  )

  // ---- 4. 格 (lattice): LLL --------------------------------------------
  let basis = [[1, 1, 1], [0 - 1, 0, 2], [3, 5, 6]]
  let red = @lat.lll_reduce(basis, 0.75)
  println(
    "[lat]   LLL: ||b_1||^2  \{@lat.norm2(basis[0])} -> \{@lat.norm2(red[0])}, same lattice = \{@lat.same_lattice(basis, red)}",
  )

  // ---- 5. 泰希米勒空間 (Teichmuller space) -----------------------------
  let (a, b) = @teich.modular_torus()
  let ab = @teich.m2_mul(a, b)
  let (x, y, z) = (@teich.m2_tr(a), @teich.m2_tr(b), @teich.m2_tr(ab))
  println(
    "[teich] (tr A, tr B, tr AB) at the modular torus      = (\{x}, \{y}, \{z})",
  )
  println(
    "[teich] Fricke tr[A,B] = x^2+y^2+z^2-xyz-2            = \{@teich.fricke_commutator_trace(x, y, z)}",
  )
  println(
    "[teich] McShane sum over |p|,|q| <= 8                 = \{@teich.mcshane_partial(a, b, 8)}  (limit 1/2)",
  )
  let (tw_a, tw_b) = @teich.fn_twist(a, b, 0.35)
  println(
    "[teich] Fenchel-Nielsen twist t = 0.35: tr A = \{@teich.m2_tr(tw_a)}, tr B = \{@teich.m2_tr(tw_b)}",
  )

  // ---- 6. 值 (valuations): Hensel and Newton polygons ------------------
  let r7 = @valued.padic_sqrt(2, 7, 10)
  println(
    "[valued] sqrt(2) in Z_7 to 10 digits                   = \{r7}   (residue: \{@nf.mod_pos(@valued.mulmod(r7, r7, @valued.ipow(7, 10)) - 2, @valued.ipow(7, 10))})",
  )
  let f = @valued.poly_mul(@valued.poly_mul([0 - 1, 1], [0 - 2, 1]), [0 - 8, 1])
  println(
    "[valued] Newton polygon of (x-1)(x-2)(x-8)              = \{show_triples(@valued.newton_root_valuations(f, 2))}",
  )

  // ---- 7. 熱帶化 (tropicalization) -------------------------------------
  let tf = @trop.tropicalize(f, 2)
  println(
    "[trop]  tropical roots (Kapranov)                      = \{show_roots(@trop.trop_roots(tf))}",
  )

  // ---- 8. 導範疇 (derived category) ------------------------------------
  let cx = @derived.cx_two_term(2, [[2, 0], [0, 6]], 2)
  let h0 = @derived.homology(cx)[0]
  println(
    "[der]   H_0 of [Z^2 --diag(2,6)--> Z^2]                 = Z/\{show_ints(@derived.grp_factors(h0))}, H_1 rank \{@derived.grp_rank(@derived.homology(cx)[1])}",
  )
  let t = @derived.tor_of(12, 8)
  println(
    "[der]   Tor_0^Z(Z/12, Z/8) = Tor_1                     = Z/\{show_ints(@derived.grp_factors(t[0]))}, Tor_2 rank \{@derived.grp_rank(t[2])}",
  )
  println(
    "[der]   Ext^1_Z(Z/12, Z)                               = Z/\{show_ints(@derived.grp_factors(@derived.ext_of(12)[0]))}",
  )

  // ---- 9. 範疇化 (categorification) ------------------------------------
  println(
    "[cat]   hilbert(Lambda^2(V_5))                          = \{show_ints(@cat.hilbert(@cat.exterior_power(5, 2)))}",
  )
  println(
    "[cat]   q * [5 choose 2]_q                              = \{show_ints(@cat.poly_shift(@cat.gauss_binom(5, 2), 1))}  (at q=1: \{@cat.binomial(5, 2)})",
  )
  let fs : @cat.FinSet = [0, 1]
  let gs : @cat.FinSet = [0]
  let bij = @cat.binomial_bijection(fs, gs, 3)
  println(
    "[cat]   (A u B)^[3] bijects onto the binomial RHS       = \{bij.length()} elements → \{@cat.binomial_rhs_size(2, 1, 3)}",
  )

  // ---- 10. 尼雲維奇拓撲 (Nisnevich topology) ---------------------------
  let k : @nis.Et = [1, 2]
  let cov : @nis.Et = [1, 2, 4]
  let mor = @nis.etmor_new([0, 1, 1])
  println(
    "[nis]   family \{show_ints(cov)} → \{show_ints(k)} is Nisnevich         = \{@nis.is_nisnevich_cover(k, cov, mor)} (Zariski: \{@nis.is_zariski_cover(k, cov, mor)})",
  )
  println(
    "[nis]   a section picks, per point, a degree-1 lift     = \{show_ints(@nis.nisnevich_section(k, cov, mor))}",
  )


  // ---- 11. 層 (sheaves: sheafification, stalks, Cech, strata) ------------
  let nis_site = @sheaf.nis_split_site(3)
  let cst = @sheaf.psh_constant(nis_site, 2)
  let cst1 = @sheaf.plus(nis_site, cst)
  let cst2 = @sheaf.plus(nis_site, cst1)
  println(
    "[sheaf] constant(2) ->+ -># on the Nisnevich site     = \{show_ints(cst.fibers)} -> \{show_ints(cst1.fibers)} -> \{show_ints(cst2.fibers)}",
  )
  println(
    "[sheaf]   = locally constant sheaf on 3 points         = \{show_ints(@sheaf.locally_constant(nis_site, 2).fibers)}  (sheaf: \{@sheaf.is_sheaf(nis_site, cst2)}, F^+ sheaf: \{@sheaf.is_sheaf(nis_site, cst1)})",
  )
  // the finite model of the circle: 6 points, 18 opens
  let circle = @sheaf.finite_space_site(6, @sheaf.triangle_opens())
  let cover = circle.covers[17][0]
  println(
    "[sheaf] nerve of the circle: |N_0|,|N_1|,|N_2|        = \{@sheaf.cech_simplices(circle, cover, 0).length()}, \{@sheaf.cech_simplices(circle, cover, 1).length()}, \{@sheaf.cech_simplices(circle, cover, 2).length()}  (chi = 6-9+3 = 0)",
  )
  println(
    "[sheaf]   Betti numbers mod 2 (b_0,b_1,b_2)            = \{@sheaf.cech_betti(circle, cover, 2, 0)}, \{@sheaf.cech_betti(circle, cover, 2, 1)}, \{@sheaf.cech_betti(circle, cover, 2, 2)}",
  )
  let hcir = @sheaf.cech_cohomology(circle, cover)
  println(
    "[sheaf]   integral H^n(S^1): ranks                     = \{@derived.grp_rank(hcir[0])}, \{@derived.grp_rank(hcir[1])}, \{@derived.grp_rank(hcir[2])}  (torsion in H^1: \{@derived.grp_factors(hcir[1]).length()} factors)",
  )
  // stratification by the stalk of a constructible sheaf
  let cf = @sheaf.components_presheaf(circle, 2, [0, 1, 3, 4, 5], @sheaf.adjacency(circle, 6))
  let st = @sheaf.strata(circle, cf, 6)
  let stsz : Array[Int] = []
  for i = 0; i < st.length(); i = i + 1 {
    stsz.push(st[i].length())
  }
  println(
    "[sheaf] strata of k^{pi_0(V - {pt})}: sizes            = \{show_ints(stsz)}  (stalks: 2 on the big stratum, \{cf.fibers[@sheaf.min_open_obj(circle, 2)]} at the removed point)",
  )

  println("\n================================================================")
  println("  all statements above are re-verified by:  moon test")
  println("================================================================")
}
