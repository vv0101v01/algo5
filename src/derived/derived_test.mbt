///|
fn two(n : Int32) -> @derived.Cx {
  // 0 -> Z --x n--> Z -> 0 in degrees 1 -> 0
  @derived.cx_two_term(1, [[n]], 1)
}

///|
/// Homology rank in degree k, or 0 outside the range of degrees.
fn hrank(cx : @derived.Cx, k : Int32) -> Int32 {
  if k >= 0 && k < @derived.cx_len(cx) {
    @derived.homology_rank(cx, k)
  } else {
    0
  }
}

///|
fn grp0() -> @derived.Mat {
  @derived.grp(0, [])
}

///|
test "T1/T2 homology and the Euler-Poincare identity" {
  // 0 -> Z --x2--> Z -> 0 :  H_1 = 0, H_0 = Z/2
  let c2 = two(2)
  assert_true(@derived.is_complex(c2))
  assert_eq(@derived.homology_rank(c2, 0), 0)
  assert_eq(@derived.homology_torsion(c2, 0), [2])
  assert_eq(@derived.homology_rank(c2, 1), 0)
  assert_eq(@derived.homology_torsion(c2, 1), [])
  assert_eq(@derived.homology_euler(c2), @derived.euler_char(c2))
  // 0 -> Z --x0--> Z -> 0 :  H_1 = Z, H_0 = Z
  let c0 = two(0)
  assert_eq(@derived.homology_rank(c0, 0), 1)
  assert_eq(@derived.homology_rank(c0, 1), 1)
  // 0 -> Z --x1--> Z -> 0 is acyclic
  assert_true(@derived.is_acyclic(two(1)))
  assert_false(@derived.is_acyclic(two(2)))
  // Z^2 --diag(2,3)--> Z^2 :  H_0 = Z/2 + Z/3 = Z/6, H_1 = 0
  let c23 = @derived.cx_two_term(2, [[2, 0], [0, 3]], 2)
  assert_true(@derived.is_complex(c23))
  // the invariant-factor normal form merges Z/2 + Z/3 into Z/6
  assert_eq(@derived.homology_torsion(c23, 0), [6])
  assert_true(@derived.grp_iso(@derived.homology(c23)[0], @derived.grp(0, [6])))
  assert_eq(@derived.homology_euler(c23), @derived.euler_char(c23))
  // a genuine three-term complex: 0 -> Z --[2;0]--> Z^2 --[0,3]--> Z -> 0
  let c3 = @derived.cx_new([1, 2, 1], [
    @derived.mat_zeros(0, 1),
    [[0, 3]],
    [[2], [0]],
  ])
  assert_true(@derived.is_complex(c3))
  assert_true(@derived.grp_iso(@derived.homology(c3)[0], @derived.grp(0, [3])))
  assert_true(@derived.grp_iso(@derived.homology(c3)[1], @derived.grp(0, [2])))
  assert_true(@derived.grp_iso(@derived.homology(c3)[2], grp0()))
  assert_eq(@derived.homology_euler(c3), @derived.euler_char(c3))
  // Euler-Poincare on a family of two-term and tensor complexes
  let mut seed = 12345
  for t = 0; t < 25; t = t + 1 {
    seed = (seed * 75 + 74) % 32749
    let n = seed % 30
    seed = (seed * 75 + 74) % 32749
    let m = seed % 30
    let a = two(n)
    let b = two(m)
    assert_true(@derived.is_complex(a))
    assert_eq(@derived.homology_euler(a), @derived.euler_char(a))
    let ab = @derived.tensor_cx(a, b)
    assert_true(@derived.is_complex(ab))
    // chi(A (x) B) = chi(A) * chi(B) = 0 here, but check the identity anyway
    assert_eq(
      @derived.euler_char(ab),
      @derived.euler_char(a) * @derived.euler_char(b),
    )
    assert_eq(@derived.homology_euler(ab), @derived.euler_char(ab))
    // the split complex of any complex has the same Euler characteristic and
    // the same homology
    let sp = @derived.split_cx(ab)
    assert_true(@derived.is_complex(sp))
    assert_eq(@derived.euler_char(sp), @derived.euler_char(ab))
    let ha = @derived.homology(ab)
    let hs = @derived.homology(sp)
    assert_eq(hs.length(), ha.length() + 1)
    for k = 0; k < ha.length(); k = k + 1 {
      assert_true(@derived.grp_iso(ha[k], hs[k]))
    }
    // the extra top degree of the split complex is acyclic
    assert_true(@derived.grp_iso(hs[ha.length()], grp0()))
  }
}

///|
test "T3 mapping cones, quasi-isomorphisms and the long exact sequence" {
  // the identity is a quasi-isomorphism: its cone is contractible
  let c = two(2)
  let idm = @derived.cm_id(c)
  assert_true(@derived.is_chain_map(c, c, idm))
  assert_true(@derived.is_quasi_iso(c, c, idm))
  assert_true(@derived.is_acyclic(@derived.cone(c, c, idm)))
  // multiplication by 2 on Z (degree 0) is not a quasi-isomorphism
  let z0 = @derived.cx_zero([1])
  let f2 = @derived.cm_new([[[2]]])
  assert_true(@derived.is_chain_map(z0, z0, f2))
  assert_false(@derived.is_quasi_iso(z0, z0, f2))
  assert_true(
    @derived.grp_iso(
      @derived.homology(@derived.cone(z0, z0, f2))[0],
      @derived.grp(0, [2]),
    ),
  )
  // multiplication by 1 is
  let f1 = @derived.cm_new([[[1]]])
  assert_true(@derived.is_quasi_iso(z0, z0, f1))
  // a non-chain-map is detected: d f != f d
  let bad = @derived.cm_new([[[1], [1]]])
  let src = @derived.cx_zero([1])
  let dst = two(0)
  assert_false(@derived.is_chain_map(src, dst, bad))
  // additivity of the Euler characteristic along a distinguished triangle
  // C -> D -> Cone(f) -> C[1]
  for n in [0, 2, 3, 6] {
    let (sp, fm) = @derived.split_2term(two(n))
    assert_true(@derived.is_chain_map(sp, two(n), fm))
    assert_true(@derived.is_quasi_iso(sp, two(n), fm))
    let cone = @derived.cone(sp, two(n), fm)
    assert_true(@derived.is_complex(cone))
    assert_true(@derived.is_acyclic(cone))
    let mut acc = 0
    for k = 0; k < @derived.cx_len(cone); k = k + 1 {
      let s = if k % 2 == 0 { 1 } else { 0 - 1 }
      acc = acc + s * hrank(two(n), k)
      acc = acc - s * hrank(cone, k)
      acc = acc - s * hrank(sp, k)
    }
    // H(C) = H(split(C)), so the alternating sum vanishes
    assert_eq(acc, 0)
  }
  // shifting moves homology: H_{n+k}(C[k]) = H_n(C)
  let sh = @derived.shift(two(2), 1)
  assert_true(@derived.is_complex(sh))
  assert_eq(@derived.homology_torsion(sh, 1), [2])
  assert_eq(@derived.homology_rank(sh, 0), 0)
  assert_true(
    @derived.grp_iso(@derived.homology(sh)[1], @derived.homology(two(2))[0]),
  )
}

///|
test "T4 splitting over Z: an explicit quasi-isomorphism" {
  // for every two-term complex, the split complex comes with an explicit
  // chain map which is a quasi-isomorphism
  for n in [0, 1, 2, 3, 4, 6, 12] {
    let cx = two(n)
    let (sp, fm) = @derived.split_2term(cx)
    assert_true(@derived.is_complex(sp))
    assert_true(@derived.is_chain_map(sp, cx, fm))
    assert_true(@derived.is_quasi_iso(sp, cx, fm))
    // the split complex has zero differential except for the torsion block
    let hs = @derived.homology(sp)
    let hc = @derived.homology(cx)
    for k = 0; k < hc.length(); k = k + 1 {
      assert_true(@derived.grp_iso(hs[k], hc[k]))
    }
    // H_0 = Z^{free rank} (+) Z/n : for n = 0 the cokernel is Z, for n = 1
    // it is 0, and for n > 1 it is Z/n
    let expected0 = @derived.grp(
      if n == 0 {
        1
      } else {
        0
      },
      if n > 1 {
        [n]
      } else {
        []
      },
    )
    assert_true(@derived.grp_iso(hs[0], expected0))
    assert_true(@derived.grp_iso(hc[0], expected0))
  }
  // a two-term complex with a non-cyclic cokernel
  let cx = @derived.cx_two_term(2, [[2, 0], [0, 4]], 2)
  let (sp, fm) = @derived.split_2term(cx)
  assert_true(@derived.is_quasi_iso(sp, cx, fm))
  assert_true(
    @derived.grp_iso(@derived.homology(sp)[0], @derived.grp(0, [2, 4])),
  )
  assert_eq(@derived.homology_torsion(cx, 0), [2, 4])
  // Z/2 + Z/4 is NOT Z/8: the splitting remembers the invariant factors
  assert_false(@derived.grp_iso(@derived.grp(0, [2, 4]), @derived.grp(0, [8])))
  assert_true(@derived.grp_iso(@derived.grp(0, [2, 3]), @derived.grp(0, [6])))
  // splitting a three-term complex
  let c3 = @derived.cx_new([1, 2, 1], [
    @derived.mat_zeros(0, 1),
    [[0, 3]],
    [[2], [0]],
  ])
  let sp3 = @derived.split_cx(c3)
  assert_true(@derived.is_complex(sp3))
  assert_eq(@derived.homology(sp3).length(), 4)
  for k = 0; k < 3; k = k + 1 {
    assert_true(
      @derived.grp_iso(@derived.homology(sp3)[k], @derived.homology(c3)[k]),
    )
  }
  assert_true(@derived.grp_iso(@derived.homology(sp3)[3], grp0()))
  // the split complex has the same total rank contribution as H_*(C)
  assert_eq(@derived.homology_euler(sp3), @derived.homology_euler(c3))
}

///|
test "T5 Kunneth formula for the tensor product of complexes" {
  for n in [0, 2, 3, 5] {
    for m in [0, 4, 7] {
      let a = two(n)
      let b = two(m)
      let ab = @derived.tensor_cx(a, b)
      assert_true(@derived.is_complex(ab))
      let h = @derived.homology(ab)
      let pred = @derived.kunneth_predict(a, b)
      assert_eq(h.length(), pred.length())
      for k = 0; k < h.length(); k = k + 1 {
        assert_true(@derived.grp_iso(h[k], pred[k]))
      }
      // Euler characteristic is multiplicative
      assert_eq(
        @derived.euler_char(ab),
        @derived.euler_char(a) * @derived.euler_char(b),
      )
    }
  }
  // the group-level tensor and Tor operations
  let z2 = @derived.grp(0, [2])
  let z3 = @derived.grp(0, [3])
  let z6 = @derived.grp(0, [6])
  assert_true(@derived.grp_iso(@derived.grp_tensor(z2, z3), grp0())) // Z/2 (x) Z/3 = 0
  assert_true(@derived.grp_iso(@derived.grp_tor(z2, z3), grp0()))
  assert_true(@derived.grp_iso(@derived.grp_tor(z2, z2), z2))
  assert_true(@derived.grp_iso(@derived.grp_tor(z2, z6), z2))
  assert_true(
    @derived.grp_iso(@derived.grp_tensor(@derived.grp(1, []), z2), z2),
  )
  assert_true(
    @derived.grp_iso(
      @derived.grp_tensor(@derived.grp(2, []), @derived.grp(3, [])),
      @derived.grp(6, []),
    ),
  )
  assert_eq(
    @derived.grp_rank(
      @derived.grp_tensor(@derived.grp(2, [4]), @derived.grp(3, [6])),
    ),
    6,
  )
  // Kunneth with a one-term complex: (Z in degree 0) (x) C = C
  let one = @derived.cx_zero([1])
  let t = @derived.tensor_cx(one, two(6))
  assert_true(@derived.grp_iso(@derived.homology(t)[0], @derived.grp(0, [6])))
  assert_eq(@derived.euler_char(t), 0)
}

///|
test "T6 Tor, Ext and the universal coefficient theorem" {
  // Tor_i^Z(Z/n, Z/m) = Z/gcd(n,m) for i = 0, 1 and 0 otherwise
  for (n, m) in [(2, 3), (4, 6), (6, 9), (5, 5), (12, 8), (1, 7)] {
    let t = @derived.tor_of(n, m)
    assert_eq(t.length(), 3)
    let g = @derived.gcd_pos(n, m)
    let expect = @derived.grp(0, if g > 1 { [g] } else { [] })
    assert_true(@derived.grp_iso(t[0], expect))
    assert_true(@derived.grp_iso(t[1], expect))
    assert_true(@derived.grp_iso(t[2], grp0()))
  }
  // Ext^i_Z(Z/n, Z) = Z/n for i = 1 and 0 otherwise
  for n in [2, 3, 4, 6, 12] {
    let e = @derived.ext_of(n)
    assert_eq(e.length(), 2)
    // degree 0 of the dual complex is H^1 = Ext^1
    assert_true(@derived.grp_iso(e[0], @derived.grp(0, [n])))
    // degree 1 of the dual complex is H^0 = Hom(Z/n, Z) = 0
    assert_true(@derived.grp_iso(e[1], grp0()))
  }
  // Ext^1(Z, Z) = 0 (Z is free)
  assert_true(@derived.grp_iso(@derived.ext_of(1)[0], grp0()))
  // universal coefficient theorem:
  //   H^n(Hom(C,Z)) = Hom(H_n C, Z) (+) Ext^1(H_{n-1} C, Z)
  //   = Z^{rank H_n C} (+) torsion(H_{n-1} C)
  for n in [0, 2, 3, 6] {
    let cx = two(n)
    let dual = @derived.dual_cx(cx)
    assert_true(@derived.is_complex(dual))
    let hd = @derived.homology(dual)
    let hc = @derived.homology(cx)
    let nn = hc.length()
    for k = 0; k < hd.length(); k = k + 1 {
      let mm = nn - 1 - k
      let predicted = @derived.grp(
        if mm >= 0 {
          @derived.grp_rank(hc[mm])
        } else {
          0
        },
        if mm - 1 >= 0 {
          @derived.grp_factors(hc[mm - 1])
        } else {
          []
        },
      )
      assert_true(@derived.grp_iso(hd[k], predicted))
    }
    // concretely: H^1(Hom(C,Z)) = Hom(H_1, Z) (+) Ext^1(H_0, Z)
    assert_true(
      @derived.grp_iso(
        hd[0],
        @derived.grp(@derived.grp_rank(hc[1]), @derived.grp_factors(hc[0])),
      ),
    )
    // and H^0(Hom(C,Z)) = Hom(H_0, Z) = Z^{rank H_0}
    assert_true(
      @derived.grp_iso(hd[1], @derived.grp(@derived.grp_rank(hc[0]), [])),
    )
  }
  // and the UCT holds for a three-term complex too
  let c3 = @derived.cx_new([1, 2, 1], [
    @derived.mat_zeros(0, 1),
    [[0, 3]],
    [[2], [0]],
  ])
  let hd3 = @derived.homology(@derived.dual_cx(c3))
  let hc3 = @derived.homology(c3)
  let n3 = hc3.length()
  for k = 0; k < hd3.length(); k = k + 1 {
    let mm = n3 - 1 - k
    let predicted = @derived.grp(
      if mm >= 0 {
        @derived.grp_rank(hc3[mm])
      } else {
        0
      },
      if mm - 1 >= 0 {
        @derived.grp_factors(hc3[mm - 1])
      } else {
        []
      },
    )
    assert_true(@derived.grp_iso(hd3[k], predicted))
  }
}
