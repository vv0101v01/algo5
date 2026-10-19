///|
test "T1 Zariski < Nisnevich < etale, both inclusions strict" {
  // the point Spec F_p
  let pt : @nis.Et = [1]
  // the identity is a cover for all three topologies
  assert_true(@nis.is_etale_cover(pt, [1], @nis.etmor_new([0])))
  assert_true(@nis.is_nisnevich_cover(pt, [1], @nis.etmor_new([0])))
  assert_true(@nis.is_zariski_cover(pt, [1], @nis.etmor_new([0])))
  // F_p -> F_4 is etale but NOT Nisnevich: the residue field grows
  let m4 = @nis.etmor_new([0])
  assert_true(@nis.is_etale_cover(pt, [2], m4))
  assert_false(@nis.is_nisnevich_cover(pt, [2], m4))
  assert_false(@nis.is_zariski_cover(pt, [2], m4))
  assert_false(@nis.has_section(pt, [2], m4))
  // Spec(F_p) u Spec(F_4) -> Spec(F_p) is Nisnevich but not Zariski
  let m14 = @nis.etmor_new([0, 0])
  assert_true(@nis.is_nisnevich_cover(pt, [1, 2], m14))
  assert_false(@nis.is_zariski_cover(pt, [1, 2], m14))
  assert_true(@nis.has_section(pt, [1, 2], m14))
  // over F_4: F_4 x F_16 -> F_4 is Nisnevich, not Zariski
  let f4 : @nis.Et = [2]
  assert_true(@nis.is_nisnevich_cover(f4, [2, 4], @nis.etmor_new([0, 0])))
  assert_false(@nis.is_zariski_cover(f4, [2, 4], @nis.etmor_new([0, 0])))
  assert_false(@nis.is_nisnevich_cover(f4, [4], @nis.etmor_new([0])))
  assert_true(@nis.is_etale_cover(f4, [4], @nis.etmor_new([0])))
  // an empty family covers nothing
  assert_false(@nis.is_etale_cover(pt, [], @nis.etmor_new([])))
  // a disconnected target: F_4 x F_p
  let a2 : @nis.Et = [2, 1]
  let id2 = @nis.id_mor(a2)
  assert_true(@nis.is_zariski_cover(a2, a2, id2))
  assert_true(@nis.is_nisnevich_cover(a2, a2, id2))
  // the implications hold for *every* morphism between small algebras
  let mut checked = 0
  for a in [[1], [2], [1, 2], [2, 1], [1, 1], [3], [2, 2]] {
    for b in [[1], [2], [1, 2], [2, 1], [1, 1], [3], [4], [2, 4], [6]] {
      for m in @nis.all_morphisms(a, b) {
        let z = @nis.is_zariski_cover(a, b, m)
        let n = @nis.is_nisnevich_cover(a, b, m)
        let e = @nis.is_etale_cover(a, b, m)
        if z {
          assert_true(n)
        }
        if n {
          assert_true(e)
        }
        checked = checked + 1
      }
    }
  }
  assert_true(checked > 80)
  // the number of morphisms A -> B agrees with the embedding count
  for a in [[1], [2], [1, 2], [2, 4]] {
    for b in [[2], [4], [2, 4], [1]] {
      assert_eq(
        @nis.all_morphisms(a, b).length() > 0,
        @nis.count_maps(a, b) > 0,
      )
    }
  }
  assert_eq(@nis.count_maps([1], [2]), 1)
  assert_eq(@nis.count_maps([2], [4]), 2)
  assert_eq(@nis.count_maps([1, 2], [2]), 3)
}

///|
test "T2 base change of Nisnevich covers, and the tensor product formula" {
  let mut checked = 0
  let mut nisnevich_cases = 0
  for a in [[1], [2], [1, 2], [2, 1], [3]] {
    for b in [[1], [2], [1, 2], [1, 1], [2, 2], [4], [2, 4], [6]] {
      for m in @nis.all_morphisms(a, b) {
        if !@nis.is_etale_cover(a, b, m) {
          continue
        }
        for c in [[1], [2], [1, 2], [2, 4], [3]] {
          for t in @nis.all_morphisms(a, c) {
            let (bc, pc) = @nis.base_change(a, b, c, m, t)
            // the projections are morphisms
            assert_true(@nis.is_mor(c, bc, pc))
            // the fibre product has the expected F_p-dimension:
            //   dim = sum_i (sum_{j over i} deg B_j)(sum_{l over i} deg C_l) / deg A_i
            let mut expected = 0
            for i = 0; i < a.length(); i = i + 1 {
              let mut sb = 0
              let mut sc = 0
              for j = 0; j < b.length(); j = j + 1 {
                if @nis.etmor_get(m, j) == i {
                  sb = sb + b[j]
                }
              }
              for l = 0; l < c.length(); l = l + 1 {
                if @nis.etmor_get(t, l) == i {
                  sc = sc + c[l]
                }
              }
              expected = expected + sb * sc / a[i]
            }
            assert_eq(@nis.et_dim(bc), expected)
            // T2: a Nisnevich cover stays one after base change
            if @nis.is_nisnevich_cover(a, b, m) {
              assert_true(@nis.is_nisnevich_cover(c, bc, pc))
              nisnevich_cases = nisnevich_cases + 1
            }
            checked = checked + 1
          }
        }
      }
    }
  }
  assert_true(checked > 80)
  assert_true(nisnevich_cases > 20)
  // the tensor product of finite fields:
  //   F_{p^a} (x)_{F_{p^c}} F_{p^b} = (F_{p^lcm(a,b)})^{gcd(a,b)/c}
  let p = 2
  for (aa, bb, cc) in [(2, 2, 1), (2, 4, 2), (4, 6, 2), (3, 6, 3), (1, 4, 1)] {
    let l = @nis.lcm_pos(aa, bb)
    let mult = @nis.gcd_pos(aa, bb) / cc
    assert_eq(mult * l, aa * bb / cc)
    let _ = p
    // as algebras: A = F_{p^cc}, B = F_{p^aa}, C = F_{p^bb}
    let a : @nis.Et = [cc]
    let b : @nis.Et = [aa]
    let c : @nis.Et = [bb]
    let (bc, _pb, _pc) = @nis.fiber_product(
      a,
      b,
      c,
      @nis.etmor_new([0]),
      @nis.etmor_new([0]),
    )
    assert_eq(bc.length(), mult)
    for k = 0; k < bc.length(); k = k + 1 {
      assert_eq(bc[k], l)
    }
    // F_{p^2} (x)_{F_p} F_{p^2} = F_{p^2} x F_{p^2}: not a field
    if aa == 2 && bb == 2 && cc == 1 {
      assert_eq(bc, [2, 2])
    }
  }
}

///|
test "T3 Nisnevich covers are stable under composition" {
  let mut composed = 0
  for a in [[1], [2], [1, 2]] {
    for b in [[1, 2], [2, 2], [1, 1], [2]] {
      for m in @nis.all_morphisms(a, b) {
        if !@nis.is_nisnevich_cover(a, b, m) {
          continue
        }
        for c in [[1, 2], [2, 2], [2, 4], [1, 1, 2]] {
          for n in @nis.all_morphisms(b, c) {
            if !@nis.is_nisnevich_cover(b, c, n) {
              continue
            }
            let comp = @nis.compose_mor(b, c, m, n)
            assert_true(@nis.is_mor(a, c, comp))
            assert_true(@nis.is_nisnevich_cover(a, c, comp))
            composed = composed + 1
          }
        }
      }
    }
  }
  assert_true(composed > 5)
  // an explicit case: F_p -> F_p x F_4 -> (F_p x F_4) x F_4
  let a : @nis.Et = [1]
  let b : @nis.Et = [1, 2]
  let c : @nis.Et = [1, 2, 2]
  let m = @nis.etmor_new([0, 0])
  let n = @nis.etmor_new([0, 1, 1])
  assert_true(@nis.is_nisnevich_cover(a, b, m))
  assert_true(@nis.is_nisnevich_cover(b, c, n))
  let comp = @nis.compose_mor(b, c, m, n)
  assert_eq(comp.sigma, [0, 0, 0])
  assert_true(@nis.is_nisnevich_cover(a, c, comp))
  // an etale cover of F_p x F_4 which is not Nisnevich: the F_4 point is
  // covered only by F_16, whose residue field is a quadratic extension
  let d : @nis.Et = [1, 4]
  let nbad = @nis.etmor_new([0, 1])
  assert_true(@nis.is_etale_cover(b, d, nbad))
  assert_false(@nis.is_nisnevich_cover(b, d, nbad))
  assert_false(@nis.has_section(b, d, nbad))
}

///|
test "T4 every Nisnevich cover splits: an explicit section" {
  let mut sections = 0
  for a in [[1], [2], [1, 2], [2, 1], [1, 1]] {
    for b in [[1], [2], [1, 2], [1, 1], [2, 2], [4], [2, 4]] {
      for m in @nis.all_morphisms(a, b) {
        if !@nis.is_nisnevich_cover(a, b, m) {
          continue
        }
        let s = @nis.nisnevich_section(a, b, m)
        assert_true(@nis.is_section(a, b, m, s))
        // every entry is a point of residue degree 1 over its image
        for i = 0; i < a.length(); i = i + 1 {
          assert_eq(@nis.res_degree(a, b, m, s[i]), 1)
          assert_eq(@nis.etmor_get(m, s[i]), i)
          assert_eq(b[s[i]], a[i])
          // the number of embeddings of the residue field into itself is 1
          assert_eq(@nis.num_embeddings(a, b, m, s[i]), a[i])
        }
        // the number of sections = prod_i #{j : sigma(j) = i, res deg 1}
        let mut expected = 1
        for i = 0; i < a.length(); i = i + 1 {
          let mut cnt = 0
          for j = 0; j < b.length(); j = j + 1 {
            if @nis.etmor_get(m, j) == i && @nis.res_degree(a, b, m, j) == 1 {
              cnt = cnt + 1
            }
          }
          expected = expected * cnt
        }
        // every one of the enumerated sections is a genuine section, and the
        // count is the product of the numbers of splitting points
        let cur : Array[Int32] = Array::make(a.length(), 0)
        assert_eq(count_sections(a, b, m, 0, cur), expected)
        sections = sections + 1
      }
    }
  }
  assert_eq(sections, 10)
  // an etale cover that is not Nisnevich has no section
  assert_false(@nis.has_section([1], [2], @nis.etmor_new([0])))
  assert_false(@nis.has_section([2], [4], @nis.etmor_new([0])))
  assert_true(@nis.has_section([1], [1, 2], @nis.etmor_new([0, 0])))
}

///|
/// Enumerate every section of a Nisnevich cover and count them.
fn count_sections(
  a : @nis.Et,
  b : @nis.Et,
  m : @nis.EtMor,
  i : Int32,
  cur : Array[Int32],
) -> Int32 {
  if i == a.length() {
    if @nis.is_section(a, b, m, cur) {
      1
    } else {
      0
    }
  } else {
    let mut acc = 0
    for j = 0; j < b.length(); j = j + 1 {
      if @nis.etmor_get(m, j) == i && @nis.res_degree(a, b, m, j) == 1 {
        cur[i] = j
        acc = acc + count_sections(a, b, m, i + 1, cur)
      }
    }
    acc
  }
}

///|
test "T5 descent: the sheaf axiom for locally constant functions" {
  let a : @nis.Et = [1, 2]
  let b : @nis.Et = [1, 2, 2]
  let m = @nis.etmor_new([0, 1, 1])
  assert_true(@nis.is_nisnevich_cover(a, b, m))
  // a section coming from A pulls back and descends back to itself
  for s in [[0, 1], [1, 0], [2, 2], [5, 7]] {
    let pb = @nis.pullback(a, b, m, s)
    assert_eq(pb, [s[0], s[1], s[1]])
    assert_true(@nis.descends(a, b, m, pb))
    let back = @nis.descend_section(a, b, m, pb)
    assert_true(@nis.sect_eq(back, s))
    assert_true(@nis.sect_eq(@nis.pullback(a, b, m, back), pb))
  }
  // a section that is not constant on the fibres does NOT descend
  let bad = [0, 1, 2]
  assert_false(@nis.descends(a, b, m, bad))
  let bad2 = [1, 1, 2]
  assert_false(@nis.descends(a, b, m, bad2))
  // systematic check: descent holds exactly for fibrewise-constant sections
  let mut checked = 0
  for v0 = 0; v0 < 2; v0 = v0 + 1 {
    for v1 = 0; v1 < 2; v1 = v1 + 1 {
      for v2 = 0; v2 < 2; v2 = v2 + 1 {
        let s = [v0, v1, v2]
        let constant_on_fibres = v1 == v2
        assert_eq(@nis.descends(a, b, m, s), constant_on_fibres)
        checked = checked + 1
      }
    }
  }
  assert_eq(checked, 8)
  // for a family that is not surjective, descent is not unique: two different
  // sections of A can have the same pullback
  let a2 : @nis.Et = [1, 1]
  let b2 : @nis.Et = [1]
  let m2 = @nis.etmor_new([0])
  assert_false(@nis.is_surjective(a2, b2, m2))
  let s1 = [3, 4]
  let s2 = [3, 9]
  assert_true(
    @nis.sect_eq(@nis.pullback(a2, b2, m2, s1), @nis.pullback(a2, b2, m2, s2)),
  )
  assert_false(@nis.sect_eq(s1, s2))
  // but for a Nisnevich (hence surjective) cover the descent is unique
  for s in [[0, 1], [1, 0], [4, 4]] {
    let pb = @nis.pullback(a, b, m, s)
    let back = @nis.descend_section(a, b, m, pb)
    assert_true(@nis.sect_eq(back, s))
  }
  // and the fibre product is exactly the equivalence relation "same image"
  let (bc, pb2, pc2) = @nis.fiber_product(a, b, b, m, m)
  assert_true(@nis.is_mor(b, bc, pb2))
  assert_true(@nis.is_mor(b, bc, pc2))
  let mut agree = 0
  for k = 0; k < bc.length(); k = k + 1 {
    assert_eq(
      @nis.etmor_get(m, @nis.etmor_get(pb2, k)),
      @nis.etmor_get(m, @nis.etmor_get(pc2, k)),
    )
    agree = agree + 1
  }
  assert_eq(agree, 5) // 1 pair over the point of degree 1, 2x2 over degree 2
}
