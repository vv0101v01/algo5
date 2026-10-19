///|
fn deg_of(v : Array[Int32], idx : Int32) -> Int32 {
  let mut acc = 0
  for d = 0; d < v.length(); d = d + 1 {
    if idx < acc + v[d] {
      return d
    }
    acc = acc + v[d]
  }
  abort("deg_of: out of range")
}

///|
fn set_of(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    out.push(i)
  }
  out
}

///|
test "T1 FinSet categorifies N: isomorphism = equality of cardinality" {
  // 同構即相同 for finite sets: A ≅ B  ⟺  |A| = |B|
  let universe = [0, 1, 2, 3]
  let mut compared = 0
  for m1 = 0; m1 < 16; m1 = m1 + 1 {
    for m2 = 0; m2 < 16; m2 = m2 + 1 {
      let a : Array[Int32] = []
      let b : Array[Int32] = []
      for i = 0; i < 4; i = i + 1 {
        if m1 / @cat.ipow(2, i) % 2 == 1 {
          a.push(universe[i])
        }
        if m2 / @cat.ipow(2, i) % 2 == 1 {
          b.push(universe[i])
        }
      }
      let nbij = @cat.count_bijections(a, b)
      let iso = nbij > 0
      assert_eq(iso, a.length() == b.length())
      if a.length() == b.length() {
        // the number of isomorphisms is the factorial of the cardinality
        assert_eq(nbij, @cat.factorial(a.length()))
      }
      compared = compared + 1
    }
  }
  assert_eq(compared, 256)
  // decategorified arithmetic
  let a = [0, 1, 2]
  let b = [7, 8]
  assert_eq(
    @cat.cardinality(@cat.coproduct(a, b)),
    @cat.cardinality(a) + @cat.cardinality(b),
  )
  assert_eq(
    @cat.cardinality(@cat.product(a, b)),
    @cat.cardinality(a) * @cat.cardinality(b),
  )
  assert_eq(
    @cat.cardinality(@cat.exponential(a, b)),
    @cat.ipow(@cat.cardinality(b), @cat.cardinality(a)),
  )
  assert_eq(@cat.count_bijections(a, a), 6)
  // disjointness of the coproduct injections
  assert_true(@cat.is_left(@cat.inl(5)))
  assert_false(@cat.is_left(@cat.inr(5)))
  assert_eq(@cat.from_inl(@cat.inl(5)), 5)
  assert_eq(@cat.from_inr(@cat.inr(5)), 5)
  assert_eq(@cat.pfst(@cat.pair(3, 7)), 3)
  assert_eq(@cat.psnd(@cat.pair(3, 7)), 7)
}

///|
test "T1 the cartesian closed structure of FinSet: three explicit bijections" {
  for na = 1; na <= 3; na = na + 1 {
    for nb = 1; nb <= 2; nb = nb + 1 {
      for nc = 1; nc <= 3; nc = nc + 1 {
        let a = set_of(na)
        let b = set_of(nb)
        let c = set_of(nc)
        // C^(A+B) ≅ C^A × C^B
        let f1 = @cat.curry_coproduct(a, b, c)
        let d1 = @cat.exponential(@cat.coproduct(a, b), c)
        let cd1 = @cat.product(@cat.exponential(a, c), @cat.exponential(b, c))
        assert_true(@cat.is_bijection_onto(f1, d1, cd1))
        // (A × B)^C ≅ A^C × B^C
        let f2 = @cat.product_exponential(a, b, c)
        let d2 = @cat.exponential(c, @cat.product(a, b))
        let cd2 = @cat.product(@cat.exponential(c, a), @cat.exponential(c, b))
        assert_true(@cat.is_bijection_onto(f2, d2, cd2))
        // (C^B)^A ≅ C^(B × A)
        if @cat.ipow(nc, nb) <= 27 {
          let f3 = @cat.curry_exponential(a, b, c)
          let d3 = @cat.exponential(a, @cat.exponential(b, c))
          let cd3 = @cat.exponential(@cat.product(b, a), c)
          assert_true(@cat.is_bijection_onto(f3, d3, cd3))
        }
      }
    }
  }
}

///|
test "T1 the categorified binomial theorem" {
  for (na, nb, n) in [(1, 1, 3), (2, 1, 3), (1, 2, 4), (2, 2, 3), (3, 1, 3)] {
    let a = set_of(na)
    let b = set_of(nb)
    let dom = @cat.functions_from_n(a, b, n)
    let f = @cat.binomial_bijection(a, b, n)
    assert_eq(f.length(), dom.length())
    assert_eq(dom.length(), @cat.ipow(na + nb, n))
    // injective: all the images are distinct
    let seen : Array[Int32] = []
    for y in f {
      for s in seen {
        assert_true(y != s)
      }
      seen.push(y)
    }
    // and the cardinalities agree with the decategorified identity
    assert_eq(@cat.binomial_rhs_size(na, nb, n), @cat.ipow(na + nb, n))
    assert_true(@cat.decategorified_binomial(na, nb, n))
    // the encoding is injective in its parameters
    let e1 = @cat.binomial_encode(n, 1, 1, 0, 0, na, nb)
    let e2 = @cat.binomial_encode(n, 2, 1, 0, 0, na, nb)
    assert_true(e1 != e2)
  }
  // the number of k-subsets is the binomial coefficient
  for n = 0; n <= 6; n = n + 1 {
    for k = 0; k <= n; k = k + 1 {
      assert_eq(@cat.subsets_of_size(n, k).length(), @cat.binomial(n, k))
    }
  }
}

///|
test "T2 graded vector spaces categorify the Gaussian binomials" {
  // Lambda^n(V_d) has Hilbert series q^{n(n-1)/2} [d choose n]_q
  for d = 1; d <= 6; d = d + 1 {
    for n = 0; n <= d; n = n + 1 {
      let lhs = @cat.hilbert(@cat.exterior_power(d, n))
      let rhs = @cat.poly_shift(@cat.gauss_binom(d, n), n * (n - 1) / 2)
      assert_true(@cat.poly_eq(lhs, rhs))
      // the total dimension is the ordinary binomial coefficient
      let mut tot = 0
      for x in lhs {
        tot = tot + x
      }
      assert_eq(tot, @cat.binomial(d, n))
    }
    // Lambda^d(V_d) = q^{d(d-1)/2}: the determinant line
    assert_true(
      @cat.poly_eq(
        @cat.hilbert(@cat.exterior_power(d, d)),
        @cat.poly_shift([1], d * (d - 1) / 2),
      ),
    )
    // Lambda^n(V_d) = 0 for n > d
    assert_eq(@cat.grv_dim(@cat.exterior_power(d, d + 1)), 0)
  }
  // S^n(V_d) has Hilbert series [d+n-1 choose n]_q
  for d = 1; d <= 4; d = d + 1 {
    for n = 1; n <= 4; n = n + 1 {
      let lhs = @cat.hilbert(@cat.symmetric_power(d, n))
      let rhs = @cat.gauss_binom(d + n - 1, n)
      assert_true(@cat.poly_eq(lhs, rhs))
      // and its total dimension is the multiset coefficient
      let mut tot = 0
      for x in lhs {
        tot = tot + x
      }
      assert_eq(tot, @cat.binomial(d + n - 1, n))
    }
  }
  // the Gaussian binomial specialises to the ordinary one at q = 1
  for d = 1; d <= 6; d = d + 1 {
    for n = 0; n <= d; n = n + 1 {
      let mut tot = 0
      for x in @cat.gauss_binom(d, n) {
        tot = tot + x
      }
      assert_eq(tot, @cat.binomial(d, n))
    }
  }
}

///|
test "T2 同構即相同 for graded vector spaces: Hilbert series = iso class" {
  // V_d (x) V_e and the explicit isomorphism
  for d = 1; d <= 4; d = d + 1 {
    for e = 1; e <= 4; e = e + 1 {
      let v = @cat.grv_tensor(@cat.grv_standard(d), @cat.grv_standard(e))
      let w = @cat.grv_tensor(@cat.grv_standard(e), @cat.grv_standard(d))
      assert_true(@cat.grv_iso(v, w))
      let iso = @cat.grv_isomorphism(v, w)
      assert_eq(iso.length(), @cat.grv_dim(v))
      // the constructed isomorphism really does preserve the degree
      for k = 0; k < iso.length(); k = k + 1 {
        let (i, j) = iso[k]
        assert_eq(deg_of(v, i), deg_of(w, j))
      }
      // v and the "same" space with a different grading are not isomorphic
      let other = @cat.poly_shift(@cat.grv_standard(d), 1)
      if !@cat.grv_iso(@cat.grv_standard(d), other) {
        assert_false(@cat.grv_iso(@cat.grv_standard(d), other))
      }
    }
  }
  // K_0(grVect) = Z[q]: [V (+) W] = [V] + [W] and [V (x) W] = [V]·[W]
  let v = @cat.grv_standard(3)
  let w = @cat.grv_standard(2)
  assert_eq(
    @cat.hilbert(@cat.grv_sum(v, w)),
    @cat.poly_add(@cat.hilbert(v), @cat.hilbert(w)),
  )
  assert_true(
    @cat.poly_eq(
      @cat.hilbert(@cat.grv_tensor(v, w)),
      @cat.poly_mul(@cat.hilbert(v), @cat.hilbert(w)),
    ),
  )
  // the Hilbert series of V_d is 1 + q + ... + q^{d-1}
  assert_true(@cat.poly_eq(@cat.hilbert(@cat.grv_standard(4)), [1, 1, 1, 1]))
  // an isomorphism in the other direction: Lambda^2(V_4) ≅ q·[4 choose 2]_q
  assert_true(
    @cat.poly_eq(@cat.hilbert(@cat.exterior_power(4, 2)), [0, 1, 1, 2, 1, 1]),
  )
}

///|
test "T3 K_0(D^b(Z)) = Z via the Euler characteristic" {
  // [C] computed from the chain groups equals [C] computed from the homology
  for n in [0, 1, 2, 3, 6, 12] {
    let cx = @derived.cx_two_term(1, [[n]], 1)
    assert_eq(@cat.k0_from_chains(cx), @cat.k0_from_homology(cx))
    assert_eq(@cat.k0_from_chains(cx), 0)
  }
  let c3 = @derived.cx_new([1, 2, 1], [
    @derived.mat_zeros(0, 1),
    [[0, 3]],
    [[2], [0]],
  ])
  assert_eq(@cat.k0_from_chains(c3), @cat.k0_from_homology(c3))
  assert_eq(@cat.k0_from_chains(c3), 0)
  // chi is additive along distinguished triangles: chi(D) = chi(C) + chi(Cone)
  for n in [0, 2, 3] {
    let cx = @derived.cx_two_term(1, [[n]], 1)
    let (sp, fm) = @derived.split_2term(cx)
    let cone = @derived.cone(sp, cx, fm)
    assert_eq(
      @cat.k0_from_chains(cx),
      @cat.k0_from_chains(sp) + @cat.k0_from_chains(cone),
    )
    // and it is multiplicative for tensor products
    let t = @derived.tensor_cx(cx, sp)
    assert_eq(
      @cat.k0_from_chains(t),
      @cat.k0_from_chains(cx) * @cat.k0_from_chains(sp),
    )
  }
  // K_0(FinSet) = N: cardinality is additive and multiplicative
  let a = [0, 1, 2]
  let b = [7, 8]
  assert_eq(@cat.cardinality(@cat.coproduct(a, b)), 5)
  assert_eq(@cat.cardinality(@cat.product(a, b)), 6)
  assert_eq(@cat.cardinality(@cat.exponential(a, b)), 8)
}
