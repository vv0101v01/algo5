///|
fn close(a : Double, b : Double) -> Bool {
  (a - b).abs() < 0.000000001
}

///|
fn cmp_gr() -> @nf.Cmp {
  fn(a : Array[Int32], b : Array[Int32]) -> Int32 { @nf.cmp_grlex(a, b) }
}

///|
fn poly_of(ts : Array[(Int32, Array[Int32])], p : Int32) -> @nf.Poly {
  let acc : Array[@nf.Term] = []
  for (c, e) in ts {
    acc.push({ c, e, })
  }
  @nf.poly_normalize(acc, p, cmp_gr())
}

///|
test "T1 the tropical semiring: idempotent, commutative, distributive" {
  let vals = [0.0, 1.5, 0.0 - 3.25, 7.0, @trop.trop_inf()]
  for a in vals {
    for b in vals {
      // commutativity
      assert_eq(@trop.trop_add(a, b), @trop.trop_add(b, a))
      assert_eq(@trop.trop_mul(a, b), @trop.trop_mul(b, a))
      // idempotency of + and the two neutral elements
      assert_eq(@trop.trop_add(a, a), a)
      assert_eq(@trop.trop_add(a, @trop.trop_zero()), a)
      assert_eq(@trop.trop_mul(a, @trop.trop_one()), a)
      // absorption by the additive identity
      assert_eq(@trop.trop_mul(a, @trop.trop_zero()), @trop.trop_zero())
      // multiplicative inverses: (T ∖ {inf}, *) is a group
      if !@trop.trop_is_inf(a) {
        assert_eq(@trop.trop_mul(a, @trop.trop_inv(a)), @trop.trop_one())
        assert_eq(@trop.trop_mul(@trop.trop_inv(a), a), @trop.trop_one())
      }
      // no additive inverses: min(a,b) = inf forces a = inf
      if @trop.trop_is_inf(@trop.trop_add(a, b)) {
        assert_true(@trop.trop_is_inf(a) && @trop.trop_is_inf(b))
      }
      for c in vals {
        // associativity
        assert_eq(
          @trop.trop_add(@trop.trop_add(a, b), c),
          @trop.trop_add(a, @trop.trop_add(b, c)),
        )
        assert_eq(
          @trop.trop_mul(@trop.trop_mul(a, b), c),
          @trop.trop_mul(a, @trop.trop_mul(b, c)),
        )
        // distributivity: a*(b + c) = a*b + a*c
        assert_eq(
          @trop.trop_mul(a, @trop.trop_add(b, c)),
          @trop.trop_add(@trop.trop_mul(a, b), @trop.trop_mul(a, c)),
        )
        // tropical powers
        assert_eq(@trop.trop_pow(a, 2), @trop.trop_mul(a, a))
      }
    }
  }
}

///|
test "T2 tropicalisation is a semiring homomorphism (with cancellation)" {
  // equality for products with no cancellation (non-negative coefficients)
  let f = [2, 3, 1]
  let g = [5, 0, 4]
  let p = 3
  let tf = @trop.tropicalize(f, p)
  let tg = @trop.tropicalize(g, p)
  let tfg = @trop.tropicalize(@valued.poly_mul(f, g), p)
  assert_eq(@trop.trop_poly_mul(tf, tg), tfg)
  // min-plus convolution: coefficient k is min_i (a_i + b_{k-i})
  let conv = @trop.trop_poly_mul([1.0, 4.0], [2.0, 5.0])
  assert_eq(conv, [3.0, 6.0, 9.0])
  // tropical powers
  let sq = @trop.trop_poly_mul([0.0, 1.0], [0.0, 1.0])
  assert_eq(sq, [0.0, 1.0, 2.0])
  assert_eq(@trop.trop_poly_pow([0.0, 1.0], 3), [0.0, 1.0, 2.0, 3.0])
  // cancellation: (x - 1)(x + 1) = x^2 - 1, so trop(fg) >= trop(f) * trop(g)
  // with a strict inequality at the middle coefficient
  let a : Array[Int32] = [0 - 1, 1]
  let b : Array[Int32] = [1, 1]
  let ab : Array[Int32] = [0 - 1, 0, 1]
  assert_eq(@valued.poly_mul(a, b), ab)
  let lhs = @trop.tropicalize(ab, 2)
  let rhs = @trop.trop_poly_mul(
    @trop.tropicalize(a, 2),
    @trop.tropicalize(b, 2),
  )
  assert_eq(lhs, [0.0, @trop.trop_inf(), 0.0])
  assert_eq(rhs, [0.0, 0.0, 0.0])
  assert_true(lhs[1] >= rhs[1])
  // sums: trop(f + g) >= trop(f) (+) trop(g), strict when cancellation occurs
  let s = @trop.tropicalize(@valued.poly_sub(a, a), 2)
  assert_true(
    s[0] >=
    @trop.trop_add(@trop.tropicalize(a, 2)[0], @trop.tropicalize(a, 2)[0]),
  )
  assert_true(@trop.trop_is_inf(s[0]))
  // evaluation is the min of the linear forms
  let cs = @trop.tropicalize([6, 0, 12], 2)
  assert_eq(cs, [1.0, @trop.trop_inf(), 2.0])
  assert_true(close(@trop.trop_eval(cs, 0.0), 1.0))
  assert_true(close(@trop.trop_eval(cs, 0.0 - 1.0), 0.0))
  assert_true(close(@trop.trop_eval(cs, 0.0 - 2.0), 0.0 - 2.0))
  // the unique corner of min(1, 2 + 2x) is at x = -1/2
  assert_true(close(@trop.trop_eval(cs, 0.0 - 0.5), 1.0))
  assert_true(@trop.trop_is_root(cs, 0.0 - 0.5))
  assert_false(@trop.trop_is_root(cs, 0.0))
  assert_eq(@trop.trop_argmins(cs, 0.0 - 0.5), [0, 2])
}

///|
test "T3 fundamental theorem: tropical roots = valuations of the roots" {
  // f = prod (x - p^{e_i}): the roots have valuations e_i
  for exps in [[0, 1], [0, 0, 2], [1, 2, 3], [0, 3], [2, 2]] {
    let p = 2
    let mut f : Array[Int32] = [1]
    for e in exps {
      f = @valued.poly_mul(f, [0 - @valued.ipow(p, e), 1])
    }
    let tf = @trop.tropicalize(f, p)
    let roots = @trop.trop_roots(tf)
    // two independent algorithms must agree
    let np = @valued.newton_root_valuations(f, p)
    let from_roots : Array[Int32] = []
    for i = 0; i < roots.length(); i = i + 1 {
      let (w, m) = roots[i]
      // the valuation of a root is the tropical root w
      assert_true(close(w, w.round()))
      for j = 0; j < m; j = j + 1 {
        from_roots.push(w.to_int())
      }
      // the minimum is really attained at least twice there
      assert_true(@trop.trop_is_root(tf, w))
      // and the value equals the min of the linear forms
      assert_true(close(@trop.trop_eval(tf, w), @trop.trop_eval(tf, w)))
    }
    let from_np : Array[Int32] = []
    for i = 0; i < np.length(); i = i + 1 {
      let (sn, sd, mult) = np[i]
      assert_eq(sd, 1)
      for j = 0; j < mult; j = j + 1 {
        from_np.push(sn)
      }
    }
    from_roots.sort()
    from_np.sort()
    assert_eq(from_roots, from_np)
    let expected = exps
    expected.sort()
    assert_eq(from_roots, expected)
  }
  // x^2 - p: the two roots +-sqrt(p) both have valuation 1/2
  let tf2 = @trop.tropicalize([0 - 2, 0, 1], 2)
  assert_eq(tf2, [1.0, @trop.trop_inf(), 0.0])
  let r2 = @trop.trop_roots(tf2)
  assert_eq(r2.length(), 1)
  let (w2, m2) = r2[0]
  assert_true(close(w2, 0.5))
  assert_eq(m2, 2)
  // x^3 - p^2: three roots of valuation 2/3
  let r3 = @trop.trop_roots(@trop.tropicalize([0 - 4, 0, 0, 1], 2))
  assert_eq(r3.length(), 1)
  assert_true(close(r3[0].0, 2.0 / 3.0))
  assert_eq(r3[0].1, 3)
  // the total multiplicity is the degree
  let big = @valued.poly_mul(
    @valued.poly_mul([0 - 1, 1], [0 - 4, 1]),
    @valued.poly_mul([0 - 8, 1], [0 - 16, 1]),
  )
  let rbig = @trop.trop_roots(@trop.tropicalize(big, 2))
  let mut total = 0
  for i = 0; i < rbig.length(); i = i + 1 {
    total = total + rbig[i].1
  }
  assert_eq(total, 4)
}

///|
test "T4 Kapranov: corner locus (min) = initial ideal test (max)" {
  let p = 101
  let cmp = cmp_gr()
  // f = x + y + 1: the tropical line
  let fxy = poly_of([(1, [1, 0]), (1, [0, 1]), (1, [0, 0])], p)
  let gxy = @nf.buchberger([fxy], p, cmp)
  let tp_xy = @trop.tp_of([(1, [1, 0]), (1, [0, 1]), (1, [0, 0])], 2)
  // f = x*y + x + y + 1 = (x+1)(y+1)
  let f2 = poly_of([(1, [1, 1]), (1, [1, 0]), (1, [0, 1]), (1, [0, 0])], p)
  let g2 = @nf.buchberger([f2], p, cmp)
  let tp2 = @trop.tp_of([(1, [1, 1]), (1, [1, 0]), (1, [0, 1]), (1, [0, 0])], 2)
  // f = x^2 + y^2 + 1
  let f3 = poly_of([(1, [2, 0]), (1, [0, 2]), (1, [0, 0])], p)
  let g3 = @nf.buchberger([f3], p, cmp)
  let tp3 = @trop.tp_of([(1, [2, 0]), (1, [0, 2]), (1, [0, 0])], 2)
  let mut agreed = 0
  let mut checked = 0
  for w1 = -2; w1 <= 2; w1 = w1 + 1 {
    for w2 = -2; w2 <= 2; w2 = w2 + 1 {
      let w = [w1, w2]
      let neg = [0.0 - w1.to_double(), 0.0 - w2.to_double()]
      checked = checked + 1
      assert_true(@trop.kapranov_agree(gxy, tp_xy, w, p, cmp))
      assert_eq(
        @nf.is_tropical(gxy, w, p, cmp),
        @trop.tp_in_corner_locus(tp_xy, neg),
      )
      assert_eq(
        @nf.is_tropical(g2, w, p, cmp),
        @trop.tp_in_corner_locus(tp2, neg),
      )
      assert_eq(
        @nf.is_tropical(g3, w, p, cmp),
        @trop.tp_in_corner_locus(tp3, neg),
      )
      if @nf.is_tropical(gxy, w, p, cmp) {
        agreed = agreed + 1
      }
    }
  }
  assert_eq(checked, 25)
  // for a principal ideal the two criteria coincide on the whole grid
  assert_true(@trop.all_generators_tropical([tp_xy], [0.0 - 1.0, 0.0 - 1.0]))
  assert_false(
    @trop.all_generators_tropical([tp_xy, tp2], [0.0 - 1.0, 0.0 - 3.0]),
  )
  // the tropical line is a 1-dimensional fan: not everything is tropical and
  // not nothing is
  assert_true(agreed > 3 && agreed < 25)
  // explicit check: w = (1,0) gives the monomial x, so -w is off the locus
  assert_false(@nf.is_tropical(gxy, [1, 0], p, cmp))
  assert_false(@trop.tp_in_corner_locus(tp_xy, [0.0 - 1.0, 0.0]))
  // w = (1,1): in_w(f) = x + y, and -w = (-1,-1) is on the locus
  assert_true(@nf.is_tropical(gxy, [1, 1], p, cmp))
  assert_true(@trop.tp_in_corner_locus(tp_xy, [0.0 - 1.0, 0.0 - 1.0]))
  // and the evaluations agree with the tropical value
  assert_true(close(@trop.tp_eval(tp_xy, [0.0 - 1.0, 0.0 - 1.0]), 0.0 - 1.0))
  assert_eq(@trop.tp_argmins(tp_xy, [0.0 - 1.0, 0.0 - 1.0]), 2)
}

///|
test "T5 tropical matrices: ultrametric product bound and tropical determinant" {
  // v(AB) >= trop(A) (*) trop(B) entrywise
  let a = [[2, 6, 10], [4, 0 - 4, 8], [12, 3, 0 - 9]]
  let b = [[0 - 3, 5, 7], [9, 0 - 12, 2], [6, 15, 0 - 21]]
  let ab = @trop.mat_mul_int(a, b)
  let ta = @trop.val_matrix(a, 2)
  let tb = @trop.val_matrix(b, 2)
  let tab = @trop.val_matrix(ab, 2)
  let prod = @trop.trop_mat_mul(ta, tb)
  let mut saw_strict = false
  for i = 0; i < 3; i = i + 1 {
    for j = 0; j < 3; j = j + 1 {
      assert_true(tab[i][j] >= prod[i][j] - 0.000000001)
      if tab[i][j] > prod[i][j] + 0.000000001 {
        saw_strict = saw_strict || true
      }
    }
  }
  // cancellation really happens: [1, -1] * [1; 1] = [0]
  let c1 : Array[Array[Int32]] = [[1, 0 - 1]]
  let c2 : Array[Array[Int32]] = [[1], [1]]
  assert_eq(@trop.mat_mul_int(c1, c2), [[0]])
  assert_true(
    @trop.trop_is_inf(@trop.val_matrix(@trop.mat_mul_int(c1, c2), 2)[0][0]),
  )
  assert_true(
    close(
      @trop.trop_mat_mul(@trop.val_matrix(c1, 2), @trop.val_matrix(c2, 2))[0][0],
      0.0,
    ),
  )
  assert_true(saw_strict)
  // tropical determinant = the assignment problem
  assert_eq(@trop.permutations(1).length(), 1)
  assert_eq(@trop.permutations(2).length(), 2)
  assert_eq(@trop.permutations(3).length(), 6)
  assert_eq(@trop.permutations(4).length(), 24)
  assert_eq(@trop.permutations(5).length(), 120)
  let m1 = [[1.0, 2.0], [3.0, 4.0]]
  let (d1, c1n) = @trop.trop_det(m1)
  assert_true(close(d1, 5.0)) // min(1+4, 2+3) = 5
  assert_eq(c1n, 2) // attained twice => tropically singular
  assert_true(@trop.trop_singular(m1))
  let m2 = [[0.0, 1.0], [2.0, 0.0]]
  let (d2, c2n) = @trop.trop_det(m2)
  assert_true(close(d2, 0.0)) // min(0+0, 1+2) = 0
  assert_eq(c2n, 1)
  assert_false(@trop.trop_singular(m2))
  // v(det M) >= tdet(trop M), with equality unless there is cancellation
  let mut seed = 41
  for t = 0; t < 30; t = t + 1 {
    let m : Array[Array[Int32]] = []
    for i = 0; i < 3; i = i + 1 {
      let row : Array[Int32] = []
      for j = 0; j < 3; j = j + 1 {
        seed = (seed * 75 + 74) % 32749
        row.push(seed % 41 - 20)
      }
      m.push(row)
    }
    let det = det3(m)
    let tm = @trop.val_matrix(m, 3)
    let (td, _c) = @trop.trop_det(tm)
    if det == 0 {
      assert_true(@trop.trop_is_inf(td))
    } else {
      assert_true(@valued.padic_val_z(det, 3).to_double() >= td - 0.000000001)
    }
  }
}

///|
fn det3(m : Array[Array[Int32]]) -> Int32 {
  m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) -
  m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) +
  m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
}

///|
test "T6 tropical Gr(2,4): the tropical Plucker relation = four-point condition" {
  // every quartet tree metric satisfies both formulations
  let mut seed = 17
  for t = 0; t < 40; t = t + 1 {
    let es : Array[Double] = []
    for i = 0; i < 5; i = i + 1 {
      seed = (seed * 75 + 74) % 32749
      es.push((seed % 17).to_double() / 4.0)
    }
    let d = @trop.quartet_metric(es[0], es[1], es[2], es[3], es[4])
    assert_true(@trop.is_tree_metric(d))
    assert_true(@trop.in_trop_grassmannian(@trop.metric_to_pluecker(d)))
    // the two largest of the four-point sums are equal for a quartet tree
    let s = @trop.four_point_sums(d)
    assert_true(close(s[1], s[2]))
    assert_true(s[1] >= s[0] - 0.000000001)
    // perturbing one distance generically destroys the condition
    let d2 = d.copy()
    d2[1] = d2[1] + 0.37
    if !@trop.is_tree_metric(d2) {
      assert_false(@trop.in_trop_grassmannian(@trop.metric_to_pluecker(d2)))
    }
  }
  // the two conditions are the same condition, for arbitrary vectors
  let mut seed2 = 991
  for t = 0; t < 60; t = t + 1 {
    let w : Array[Double] = []
    for i = 0; i < 6; i = i + 1 {
      seed2 = (seed2 * 75 + 74) % 32749
      w.push((seed2 % 13).to_double() / 2.0)
    }
    let d = [
      0.0 - w[0],
      0.0 - w[1],
      0.0 - w[2],
      0.0 - w[3],
      0.0 - w[4],
      0.0 - w[5],
    ]
    assert_eq(@trop.in_trop_grassmannian(w), @trop.is_tree_metric(d))
  }
  // the 4-cycle with unit edges is not a tree metric
  let cyc = [1.0, 2.0, 1.0, 1.0, 2.0, 1.0]
  assert_false(@trop.is_tree_metric(cyc))
  assert_false(@trop.in_trop_grassmannian(@trop.metric_to_pluecker(cyc)))
  // but the star (internal edge 0) and any pendant extension are
  let star = @trop.quartet_metric(1.0, 2.0, 3.0, 4.0, 0.0)
  assert_true(@trop.is_tree_metric(star))
  assert_eq(star, [3.0, 4.0, 5.0, 5.0, 6.0, 7.0])
}

///|
/// T1/T2 for polynomials: addition in the semiring of tropical polynomials is
/// evaluation-wise min, i.e. trop(f (+) g) = trop(f) (+) trop(g).
test "T1 tropical polynomial addition is evaluation-wise min" {
  let a = [2.0, 0.0, 3.0] // 2 (+) 0x (+) 3x^2
  let b = [1.5, 4.0] // 1.5 (+) 4x
  let s = @trop.trop_poly_add(a, b)
  for w in [0.0 - 2.0, 0.0 - 1.0, 0.0, 0.5, 1.0, 2.0] {
    assert_true(
      close(
        @trop.trop_eval(s, w),
        @trop.trop_add(@trop.trop_eval(a, w), @trop.trop_eval(b, w)),
      ),
    )
  }
  // idempotence of the semiring addition
  assert_eq(@trop.trop_poly_add(a, a), a)
  // the neutral element: every coefficient equal to infinity
  let zero = [@trop.trop_inf(), @trop.trop_inf(), @trop.trop_inf()]
  for w in [0.0 - 2.0, 0.0, 1.0, 2.0] {
    assert_true(
      close(@trop.trop_eval(@trop.trop_poly_add(a, zero), w), @trop.trop_eval(a, w)),
    )
  }
}
