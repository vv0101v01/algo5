
///|
/// A small-state Lehmer generator: Int is 32 bits, so the modulus is kept
/// below 2^15 and the multiplier below 2^7 to guarantee no overflow.
fn next_seed(s : Int32) -> Int32 {
  (s * 75 + 74) % 32749
}

///|
/// A deterministic pseudo-random positive rational, used to sample many cases.
fn rand_rational(seed : Int32, size : Int32) -> (Int32, Int32) {
  let s1 = next_seed(seed)
  let s2 = next_seed(s1)
  let n = s1 % size + 1
  let d = s2 % size + 1
  let g = @tl.igcd(n, d)
  (n / g, d / g)
}

///|
test "T1 Ostrowski product formula: |x|_inf * prod_p |x|_p = 1" {
  // exact rational arithmetic: prod_{p <= B} |x|_p = (n, d) with n*num = d*den
  for (num, den) in [(12, 5), (7, 3), (100, 7), (2, 9), (1000, 11), (17, 13)] {
    let (n, d) = @valued.padic_norm_product(num, den, 97)
    assert_eq(n * num, d * den)
    assert_true(
      (@valued.product_formula(num, den, 97) - 1.0).abs() < 0.000000000001,
    )
  }
  // the formula is *not* vacuous: truncating the product before the largest
  // prime factor of x gives something different from 1
  let (n2, d2) = @valued.padic_norm_product(12, 5, 3)
  assert_true(n2 * 12 != d2 * 5)
  // but including 5 is enough
  let (n3, d3) = @valued.padic_norm_product(12, 5, 5)
  assert_eq(n3 * 12, d3 * 5)
  // |x|_p = 1 for every prime not dividing num*den
  assert_eq(@valued.padic_val_q(12, 5, 7), 0)
  assert_true(@valued.padic_norm(12, 5, 7) - 1.0 < 0.000000001)
  // multiplicativity of the p-adic norm: |xy|_p = |x|_p |y|_p
  let mut seed = 7
  for i = 0; i < 40; i = i + 1 {
    let (n1, d1) = rand_rational(seed, 60)
    seed = next_seed(seed)
    let (n2, d2) = rand_rational(seed, 60)
    seed = next_seed(seed)
    let p = [2, 3, 5, 7, 11][i % 5]
    let lhs = @valued.padic_norm(n1 * n2, d1 * d2, p)
    let rhs = @valued.padic_norm(n1, d1, p) * @valued.padic_norm(n2, d2, p)
    assert_true((lhs - rhs).abs() < 0.000000001)
    // v(xy) = v(x) + v(y)
    assert_eq(
      @valued.padic_val_q(n1 * n2, d1 * d2, p),
      @valued.padic_val_q(n1, d1, p) + @valued.padic_val_q(n2, d2, p),
    )
  }
}

///|
test "T2 strong triangle inequality (ultrametric)" {
  let mut seed = 13
  let mut strict = 0
  for i = 0; i < 200; i = i + 1 {
    let (n1, d1) = rand_rational(seed, 40)
    seed = next_seed(seed)
    let (n2, d2) = rand_rational(seed, 40)
    seed = next_seed(seed)
    let p = [2, 3, 5, 7][i % 4]
    let (x, y, s) = @valued.ultrametric_triple(n1, d1, n2, d2, p)
    let m = if x > y { x } else { y }
    // |x + y| <= max(|x|, |y|)
    assert_true(s <= m + 0.000000001)
    if @valued.padic_val_q(n1, d1, p) != @valued.padic_val_q(n2, d2, p) {
      // unequal valuations: equality (every p-adic triangle is isosceles)
      assert_true((s - m).abs() < 0.000000001)
    } else if (s - m).abs() > 0.000000001 {
      strict = strict + 1
    }
  }
  // the strong inequality is strictly stronger than the triangle inequality:
  // e.g. 1 + (p-1) = p has |p|_p = 1/p < 1 = max(|1|_p, |p-1|_p)
  assert_true(strict > 5)
  for p in [2, 3, 5, 7, 11] {
    let (x, y, s) = @valued.ultrametric_triple(1, 1, p - 1, 1, p)
    assert_true((x - 1.0).abs() < 0.000000001)
    assert_true((y - 1.0).abs() < 0.000000001)
    assert_true((s - 1.0 / p.to_double()).abs() < 0.000000001)
  }
}

///|
test "T3 Hensel: unique lift of a simple root, p-adic sqrt, Teichmuller" {
  // x^2 - 2 over Z_7 from the root 3 mod 7
  let f : Array[Int32] = [0 - 2, 0, 1]
  assert_true(@valued.hensel_is_simple(f, 7, 3))
  let r = @valued.hensel_lift(f, 7, 3, 10)
  assert_eq(@nf.mod_pos(r - 3, 7), 0)
  let m12 = @valued.ipow(7, 10)
  assert_eq(@nf.mod_pos(@valued.mulmod(r, r, m12) - 2, m12), 0)
  // the lift is consistent: a root modulo p^k for every k <= 10
  for k = 1; k <= 10; k = k + 1 {
    let mk = @valued.ipow(7, k)
    assert_eq(@nf.mod_pos(@valued.mulmod(r, r, mk) - 2, mk), 0)
  }
  // uniqueness: among the 7^2 lifts of 3 mod 7 (mod 7^3) exactly one is a root
  let mut found = 0
  let m3 = @valued.ipow(7, 3)
  let mut a = 3
  while a < m3 {
    if @nf.mod_pos(a * a - 2, m3) == 0 {
      found = found + 1
      assert_eq(@nf.mod_pos(a - r, m3), 0)
    }
    a = a + 7
  }
  assert_eq(found, 1)
  // x^2 + 1 over Z_5: the 5-adic square root of -1
  let g : Array[Int32] = [1, 0, 1]
  assert_true(@valued.hensel_is_simple(g, 5, 2))
  let i5 = @valued.hensel_lift(g, 5, 2, 10)
  let m5 = @valued.ipow(5, 10)
  assert_eq(@nf.mod_pos(@valued.mulmod(i5, i5, m5) + 1, m5), 0)
  assert_eq(@valued.padic_sqrt(0 - 1, 5, 10), i5)
  // sqrt(2) in Z_7 agrees with the Hensel lift
  assert_eq(@valued.padic_sqrt(2, 7, 10), r)
  // x^3 - 2 over Z_5 (3^3 = 27 = 2 mod 5)
  let h : Array[Int32] = [0 - 2, 0, 0, 1]
  assert_true(@valued.hensel_is_simple(h, 5, 3))
  let c = @valued.hensel_lift(h, 5, 3, 10)
  assert_eq(
    @nf.mod_pos(@valued.mulmod(@valued.mulmod(c, c, m5), c, m5) - 2, m5),
    0,
  )
  // non-examples: no simple root modulo p
  assert_false(@valued.hensel_is_simple(f, 2, 0)) // f' = 2x = 0 mod 2
  assert_false(@valued.hensel_is_simple(g, 3, 1)) // x^2+1 has no root mod 3
  assert_false(@valued.hensel_is_simple(f, 5, 1)) // 1 - 2 = -1 mod 5
  // Teichmuller representative: omega(x)^{p-1} = 1 and omega(x) = x mod p
  for p in [3, 5, 7] {
    for x = 1; x < p; x = x + 1 {
      let w = @valued.teichmuller(x, p, 8)
      assert_eq(@nf.mod_pos(w - x, p), 0)
      assert_eq(
        @nf.mod_pos(@valued.padic_pow(w, p - 1, p, 8) - 1, @valued.ipow(p, 8)),
        0,
      )
    }
  }
}

///|
test "T4 Hensel factorisation: lift a coprime factorisation mod p" {
  // x^2 - 2 = (x - 3)(x + 3) mod 7, lifting to the genuine Z_7 factorisation
  let f2 : Array[Int32] = [0 - 2, 0, 1]
  let (g, h) = @valued.hensel_factor(f2, [0 - 3, 1], [3, 1], 7, 8)
  let m = @valued.ipow(7, 8)
  assert_eq(g.length(), 2)
  assert_eq(h.length(), 2)
  assert_eq(@nf.mod_pos(g[1] - 1, m), 0)
  assert_eq(@nf.mod_pos(h[1] - 1, m), 0)
  assert_eq(@nf.mod_pos(g[0] + 3, 7), 0)
  assert_eq(@nf.mod_pos(h[0] - 3, 7), 0)
  // the product is f modulo 7^8
  let prod = @valued.poly_mul_mod(g, h, m)
  let diff = @valued.poly_mod(@valued.poly_sub(f2, prod), m)
  for i = 0; i < diff.length(); i = i + 1 {
    assert_eq(diff[i], 0)
  }
  // and the lifted factor is x - sqrt(2): T4 is consistent with T3
  let r = @valued.padic_sqrt(2, 7, 8)
  assert_eq(g[0], @nf.mod_pos(0 - r, m))
  assert_eq(h[0], r)
  // x^4 - 1 = (x^2 - 1)(x^2 + 1) lifts to the exact rational factorisation
  let f4 : Array[Int32] = [0 - 1, 0, 0, 0, 1]
  let (g4, h4) = @valued.hensel_factor(f4, [0 - 1, 0, 1], [1, 0, 1], 5, 10)
  let m10 = @valued.ipow(5, 10)
  assert_eq(g4, [@nf.mod_pos(0 - 1, m10), 0, 1])
  assert_eq(h4, [1, 0, 1])
  assert_eq(@valued.poly_mul_mod(g4, h4, m10), @valued.poly_mod(f4, m10))
  // a genuine lift: (x - 1)(x^2 + 1) is coprime mod 3
  let f3 : Array[Int32] = [0 - 1, 1, 0 - 1, 1]
  let (g5, h5) = @valued.hensel_factor(f3, [0 - 1, 1], [1, 0, 1], 3, 12)
  let m3 = @valued.ipow(3, 12)
  let d3 = @valued.poly_mod(
    @valued.poly_sub(f3, @valued.poly_mul_mod(g5, h5, m3)),
    m3,
  )
  for i = 0; i < d3.length(); i = i + 1 {
    assert_eq(d3[i], 0)
  }
  assert_eq(@nf.mod_pos(g5[0] + 1, 3), 0)
}

///|
test "T5 Newton polygon: slopes are the valuations of the roots" {
  // f = (x - 1)(x - p): roots of valuation 0 and 1
  let p = 3
  let f1 = @valued.poly_mul([0 - 1, 1], [0 - p, 1])
  assert_eq(f1, [3, 0 - 4, 1])
  let v1 = @valued.newton_root_valuations(f1, p)
  assert_eq(v1, [(1, 1, 1), (0, 1, 1)])
  // f = x^2 - p: two roots of valuation 1/2
  let v2 = @valued.newton_root_valuations([0 - p, 0, 1], p)
  assert_eq(v2, [(1, 2, 2)])
  // f = (x-1)(x-p)(x-p^2): valuations 0, 1, 2
  let f3 = @valued.poly_mul(@valued.poly_mul([0 - 1, 1], [0 - 2, 1]), [0 - 4, 1])
  assert_eq(f3, [0 - 8, 14, 0 - 7, 1])
  let v3 = @valued.newton_root_valuations(f3, 2)
  assert_eq(v3, [(2, 1, 1), (1, 1, 1), (0, 1, 1)])
  // general family: f = prod (x - p^{e_i}) -> the root valuations are e_i
  for exps in [[0, 0, 1], [1, 2], [0, 0, 0, 3], [2, 2, 1], [0, 3, 3]] {
    let base = 2
    let mut f : Array[Int32] = [1]
    for e in exps {
      f = @valued.poly_mul(f, [0 - @valued.ipow(base, e), 1])
    }
    let got = @valued.newton_root_valuations(f, base)
    let mut total = 0
    let mut sum_vals = 0
    for i = 0; i < got.length(); i = i + 1 {
      let (sn, sd, mult) = got[i]
      total = total + mult
      // a segment of length m gives m roots of valuation sn/sd: here sd = 1
      assert_eq(sd, 1)
      for j = 0; j < mult; j = j + 1 {
        sum_vals = sum_vals + sn * mult / mult
      }
      sum_vals = sum_vals + sn * (mult - 1) * 0
    }
    // the number of roots counted with multiplicity is the degree
    assert_eq(total, exps.length())
    // v(a_0) = sum of the root valuations (f monic => a_0 = +- prod roots)
    let v0 = @valued.padic_val_z(
      @nf.mod_pos(f[0], @valued.ipow(base, 20)),
      base,
    )
    let mut expected = 0
    for e in exps {
      expected = expected + e
    }
    assert_eq(v0, expected)
    assert_eq(sum_vals, expected)
  }
  // the slopes are strictly increasing along the polygon
  let fbig = @valued.poly_mul(
    @valued.poly_mul(@valued.poly_mul([0 - 1, 1], [0 - 2, 1]), [0 - 8, 1]),
    [0 - 16, 1],
  )
  let segs = @valued.newton_polygon(fbig, 2)
  let mut prev_num = 0 - 1000000
  let mut prev_den = 1
  for i = 0; i < segs.length(); i = i + 1 {
    let (i1, v1, i2, v2) = segs[i]
    let num = v2 - v1
    let den = i2 - i1
    assert_true(num * prev_den > prev_num * den)
    prev_num = num
    prev_den = den
  }
}

///|
test "T6 valuation ring O, maximal ideal m, residue field O/m = F_p" {
  let p = 5
  let mut seed = 31
  let mut in_o = 0
  let mut in_m = 0
  let mut saw_unit = 0
  for i = 0; i < 300; i = i + 1 {
    let (n1, d1) = rand_rational(seed, 30)
    seed = next_seed(seed)
    let (n2, d2) = rand_rational(seed, 30)
    seed = next_seed(seed)
    let o1 = @valued.in_valuation_ring(n1, d1, p)
    let o2 = @valued.in_valuation_ring(n2, d2, p)
    if o1 {
      in_o = in_o + 1
      if @valued.in_maximal_ideal(n1, d1, p) {
        in_m = in_m + 1
      } else {
        saw_unit = saw_unit + 1
        // O^× = O \ m
        assert_true(@valued.is_valuation_unit(n1, d1, p))
      }
    }
    // O is a ring
    if o1 && o2 {
      assert_true(@valued.in_valuation_ring(n1 * d2 + n2 * d1, d1 * d2, p))
      assert_true(@valued.in_valuation_ring(n1 * n2, d1 * d2, p))
      // the reduction map is a ring homomorphism on O
      let r1 = @valued.residue(n1, d1, p)
      let r2 = @valued.residue(n2, d2, p)
      assert_eq(
        @valued.residue(n1 * d2 + n2 * d1, d1 * d2, p),
        @valued.residue_add(r1, r2, p),
      )
      assert_eq(
        @valued.residue(n1 * n2, d1 * d2, p),
        @valued.residue_mul(r1, r2, p),
      )
    }
    // m is an ideal: x in m, y in O  =>  xy in m
    if @valued.in_maximal_ideal(n1, d1, p) && o2 {
      assert_true(@valued.in_maximal_ideal(n1 * n2, d1 * d2, p))
    }
    // m is prime: xy in m => x in m or y in m
    if @valued.in_maximal_ideal(n1 * n2, d1 * d2, p) {
      assert_true(
        @valued.in_maximal_ideal(n1, d1, p) ||
        @valued.in_maximal_ideal(n2, d2, p),
      )
    }
  }
  assert_true(in_o > 50)
  assert_true(in_m > 5)
  assert_true(saw_unit > 20)
  // the residue map O -> F_p is surjective and its kernel is m
  let hits : Array[Int32] = Array::make(p, 0)
  for n = 1; n <= 60; n = n + 1 {
    let r = @valued.residue(n, 1, p)
    hits[r] = hits[r] + 1
    // consistency with reduction mod p for p-integral integers
    assert_eq(r, @nf.mod_pos(n, p))
  }
  for k = 0; k < p; k = k + 1 {
    assert_true(hits[k] > 0)
  }
  // ker(res) = m: x reduces to 0 iff v(x) > 0
  for n = 1; n <= 40; n = n + 1 {
    let zero = @valued.residue(n, 1, p) == 0
    assert_eq(zero, @valued.in_maximal_ideal(n, 1, p))
  }
}

///|
/// T6, continued: the ring structure lives on O = Z_p itself.  Everything the
/// theorem claims about O, m and k(v) = F_p is checked on the Z/p^N model.
test "T6 Z_p is a ring, O^x = O \\ m, and Z_p -> F_p is a homomorphism" {
  let p = 5
  let n = 4
  let m = @valued.ipow(p, n) // 625 = p^N
  let mut seed = 7
  let mut units = 0
  for i = 0; i < 200; i = i + 1 {
    let a = next_seed(seed) % m
    seed = next_seed(seed)
    let b = next_seed(seed) % m
    seed = next_seed(seed)
    let c = next_seed(seed) % m
    seed = next_seed(seed)
    // (O,+) is an abelian group
    assert_eq(
      @valued.padic_add(@valued.padic_add(a, b, p, n), c, p, n),
      @valued.padic_add(a, @valued.padic_add(b, c, p, n), p, n),
    )
    assert_eq(@valued.padic_add(a, b, p, n), @valued.padic_add(b, a, p, n))
    assert_eq(@valued.padic_add(a, 0, p, n), a)
    assert_eq(@valued.padic_add(a, @valued.padic_neg(a, p, n), p, n), 0)
    assert_eq(
      @valued.padic_sub(a, b, p, n),
      @valued.padic_add(a, @valued.padic_neg(b, p, n), p, n),
    )
    // (O,*) is a commutative monoid and distributes over +
    assert_eq(
      @valued.padic_mul(@valued.padic_mul(a, b, p, n), c, p, n),
      @valued.padic_mul(a, @valued.padic_mul(b, c, p, n), p, n),
    )
    assert_eq(@valued.padic_mul(a, b, p, n), @valued.padic_mul(b, a, p, n))
    assert_eq(@valued.padic_mul(a, 1, p, n), @valued.padic_reduce(a, p, n))
    assert_eq(
      @valued.padic_mul(a, @valued.padic_add(b, c, p, n), p, n),
      @valued.padic_add(
        @valued.padic_mul(a, b, p, n),
        @valued.padic_mul(a, c, p, n),
        p,
        n,
      ),
    )
    // O^x = {v = 0} = O \ m, and every unit is invertible in Z_p
    assert_eq(@valued.is_unit(a, p), @nf.mod_pos(a, p) != 0)
    if @valued.is_unit(a, p) {
      units = units + 1
      assert_eq(@valued.padic_mul(a, @valued.padic_inv(a, p, n), p, n), 1)
    }
    // reduction Z_p -> F_p respects + and *
    let ra = @nf.mod_pos(a, p)
    let rb = @nf.mod_pos(b, p)
    assert_eq(
      @nf.mod_pos(@valued.padic_add(a, b, p, n), p),
      @valued.residue_add(ra, rb, p),
    )
    assert_eq(
      @nf.mod_pos(@valued.padic_mul(a, b, p, n), p),
      @valued.residue_mul(ra, rb, p),
    )
  }
  assert_true(units > 100)
  // coefficient-wise reduction to Z/p^k
  let cs = [17, 0 - 3, 25, 1]
  assert_eq(
    @valued.poly_mod_pk(cs, p, 2),
    [@nf.mod_pos(17, 25), @nf.mod_pos(0 - 3, 25), @nf.mod_pos(25, 25), 1],
  )
}
