///|
fn approx(a : Double, b : Double, eps : Double) -> Bool {
  (a - b).abs() <= eps
}

///|
let eps4 = 0.0001

///|
let eps6 = 0.000001

///|
let eps7 = 0.0000001

///|
let eps8 = 0.00000001

///|
let eps9 = 0.000000001

///|
let eps10 = 0.0000000001

///|
let eps12 = 0.000000000001

///| The modular torus: the unique point of T(S_{1,1}) with all three traces

///|
/// equal, i.e. the Markoff triple (3,3,3).
test "modular torus is the Markoff point (3,3,3)" {
  let (a, b) = @teich.modular_torus()
  let ab = @teich.m2_mul(a, b)
  let x = @teich.m2_tr(a)
  let y = @teich.m2_tr(b)
  let z = @teich.m2_tr(ab)
  // representation lands in SL(2,Z) ⊂ SL(2,R)
  assert_true(approx(@teich.m2_det(a), 1.0, eps9))
  assert_true(approx(@teich.m2_det(b), 1.0, eps9))
  assert_true(approx(@teich.m2_det(ab), 1.0, eps9))
  // (x,y,z) = (3,3,3)
  assert_true(approx(x, 3.0, eps9))
  assert_true(approx(y, 3.0, eps9))
  assert_true(approx(z, 3.0, eps9))
  // the boundary curve [A,B] is parabolic: tr = -2  <=>  the Markoff cubic
  let k = @teich.m2_tr(@teich.commutator(a, b))
  assert_true(approx(k, -2.0, eps8))
  assert_true(approx(@teich.fricke_commutator_trace(x, y, z), k, eps8))
  assert_true(approx(@teich.markoff_defect(x, y, z), 0.0, eps8))
  // length of the systole: l(A) = 2 arccosh(3/2)
  assert_true(approx(@teich.length_from_trace(x), 2.0 * @math.acosh(1.5), eps9))
}

///| Theorem (Fricke).  For A,B ∈ SL(2,R) with x = tr A, y = tr B, z = tr AB,

///|        tr[A,B] = x² + y² + z² − x y z − 2 .

///| Checked on 60 random words in the free group F₂ (all of which land in

///| SL(2,Z)); the identity is an identity of polynomials, so agreement on

///|
/// many integral points is a genuine verification.
test "Fricke commutator identity on random SL(2,Z) words" {
  let (a0, b0) = @teich.modular_torus()
  let mut seed = 20261019
  let mut checked = 0
  for trial = 0; trial < 60; trial = trial + 1 {
    // LCG
    seed = (seed * 1103515245 + 12345) % 2147483647
    let n = 3 + seed % 4
    let w1 : Array[Int32] = []
    let w2 : Array[Int32] = []
    for i = 0; i < n; i = i + 1 {
      seed = (seed * 1103515245 + 12345) % 2147483647
      w1.push(seed % 4)
      seed = (seed * 1103515245 + 12345) % 2147483647
      w2.push(seed % 4)
    }
    let a = @teich.eval_word(a0, b0, w1)
    let b = @teich.eval_word(a0, b0, w2)
    let ab = @teich.m2_mul(a, b)
    // the generated matrices are genuinely in SL(2,Z)
    assert_true(approx(@teich.m2_det(a), 1.0, eps6))
    assert_true(approx(@teich.m2_det(b), 1.0, eps6))
    let x = @teich.m2_tr(a)
    let y = @teich.m2_tr(b)
    let z = @teich.m2_tr(ab)
    let lhs = @teich.m2_tr(@teich.commutator(a, b))
    assert_true(approx(@teich.fricke_commutator_trace(x, y, z), lhs, eps6))
    // tr is symmetric under swapping A and B, and tr(AB) = tr(BA)
    assert_true(approx(@teich.m2_tr(@teich.m2_mul(b, a)), z, eps6))
    checked = checked + 1
  }
  assert_eq(checked, 60)
}

///| Theorem (Fricke–Vogt).  The map

///|        T(S_{1,1}) → {(x,y,z) ∈ R³_{>2} : x² + y² + z² = x y z}

///| is a bijection, and the Vieta involutions

///|        (x,y,z) ↦ (y z − x, y, z)

///| and its permutations act on the set of Markoff triples, which is one

///| orbit.  For the once-punctured torus the traces are exactly

///|
/// 3 × {Markoff numbers} = 3 × {1, 2, 5, 13, 34, 89, …}.
test "Markoff triples: cubic, Vieta moves, 3x Markoff numbers" {
  let ts = @teich.markoff_triples(3.0, 3.0, 3.0, 200.0)
  assert_true(ts.length() > 10)
  let values : Array[Int32] = []
  for i = 0; i < ts.length(); i = i + 1 {
    let (x, y, z) = ts[i]
    // every generated triple satisfies the Markoff cubic x^2+y^2+z^2 = xyz
    assert_true(approx(@teich.markoff_defect(x, y, z), 0.0, eps9))
    // all coordinates > 2: the three curves are hyperbolic
    assert_true(x > 2.0 && y > 2.0 && z > 2.0)
    // the Vieta move in x: the two roots of t^2 - yz t + (y^2+z^2) sum to yz,
    // so the move really is an involution of the cubic surface
    assert_true(approx(@teich.vieta_x(x, y, z) + x, y * z, eps9))
    assert_true(approx(@teich.vieta_x(@teich.vieta_x(x, y, z), y, z), x, eps9))
    values.push(x.to_int())
    values.push(y.to_int())
    values.push(z.to_int())
  }
  values.sort()
  let distinct : Array[Int32] = []
  for i = 0; i < values.length(); i = i + 1 {
    if distinct.length() == 0 || distinct[distinct.length() - 1] != values[i] {
      distinct.push(values[i])
    }
  }
  // the coordinate values below 200 are exactly 3 * {1,2,5,13,29,34}
  assert_eq(distinct, [3, 6, 15, 39, 87, 102])
  // i.e. 3 * Markoff numbers 1, 2, 5, 13, 29, 34, ...
  let mm = [1, 2, 5, 13, 29, 34]
  for i = 0; i < distinct.length(); i = i + 1 {
    assert_eq(distinct[i], 3 * mm[i])
  }
  // and the Markoff numbers themselves satisfy a^2 + b^2 + c^2 = 3abc
  for i = 0; i < ts.length(); i = i + 1 {
    let (x, y, z) = ts[i]
    let a = x.to_int() / 3
    let b = y.to_int() / 3
    let c = z.to_int() / 3
    assert_eq(a * a + b * b + c * c, 3 * a * b * c)
  }
}

///| Theorem (McShane).  For every X ∈ T(S_{1,1}),

///|        Σ_γ  1 / (1 + e^{l(γ)})  =  1/2 ,

///| the sum being over all simple closed geodesics γ; and for a geodesic of

///|
/// trace x,   1/(1 + e^l) = (1 − sqrt(1 − 4/x²)) / 2 .
test "McShane identity: partial sums converge to 1/2" {
  let (a, b) = @teich.modular_torus()
  // closed form of a single term
  let term3 = @teich.mcshane_term(3.0)
  assert_true(approx(term3, (1.0 - (1.0 - 4.0 / 9.0).sqrt()) / 2.0, eps12))
  assert_true(approx(term3, 0.12732200375003505, eps12))
  // the three systoles (1,0), (0,1), (1,1) have trace 3; (1,-1) has trace 6
  let mut previous = 0.0
  for n = 1; n <= 10; n = n + 1 {
    let s = @teich.mcshane_partial(a, b, n)
    assert_true(s >= previous) // monotone: positive terms
    assert_true(s < 0.5) // converges from below
    previous = s
  }
  assert_true(approx(previous, 0.5, eps6))
  // the first shell: 3 curves of trace 3 and one of trace 6
  let m1 = @teich.mcshane_partial(a, b, 1)
  assert_true(approx(m1, 3.0 * term3 + @teich.mcshane_term(6.0), eps10))
}

///| The Stern–Brocot construction of simple closed curves: the word produced

///| for the primitive class (p,q) must abelianise back to ±(p,q) — i.e. the

///| type-level / combinatorial construction really does produce the curve of

///|
/// the requested homology class — and must be a reduced hyperbolic word.
test "curve(words): primitive classes, abelianisation, hyperbolicity" {
  let (a, b) = @teich.modular_torus()
  let mut count = 0
  for p = -5; p <= 5; p = p + 1 {
    for q = -5; q <= 5; q = q + 1 {
      if @teich.gcd_i(p, q) != 1 {
        continue
      }
      let w = @teich.curve_word(p, q)
      let (ap, aq) = @teich.abelianisation(w)
      assert_true((ap == p && aq == q) || (ap == 0 - p && aq == 0 - q))
      // reduced: free reduction is a fixed point
      assert_true(@teich.word_reduced(w))
      // hyperbolic: every simple closed curve on a hyperbolic surface has
      // length > 0, i.e. |tr| > 2
      let t = @teich.m2_tr(@teich.eval_word(a, b, w))
      assert_true(t.abs() > 2.0 + eps9)
      assert_true(
        approx(
          @teich.length_from_trace(t),
          2.0 * @math.acosh(t.abs() / 2.0),
          eps9,
        ),
      )
      count = count + 1
    }
  }
  assert_eq(count, 80)
  // re-orienting a curve does not change its length: (p,q) and (-p,-q) are
  // the same unoriented curve, hence inverse words with equal traces
  for p = 1; p <= 5; p = p + 1 {
    for q = 0; q <= 5; q = q + 1 {
      if @teich.gcd_i(p, q) != 1 {
        continue
      }
      let t1 = @teich.m2_tr(@teich.eval_word(a, b, @teich.curve_word(p, q)))
      let t2 = @teich.m2_tr(
        @teich.eval_word(a, b, @teich.curve_word(0 - p, 0 - q)),
      )
      assert_true(approx(t1, t2, eps9))
    }
  }
  // the (1,0) curve is A, the (0,1) curve is B
  assert_eq(@teich.eval_word(a, b, @teich.curve_word(1, 0)), a)
  assert_eq(@teich.eval_word(a, b, @teich.curve_word(0, 1)), b)
  // the three systoles of the modular torus all have trace 3
  for (p, q) in [(1, 0), (0, 1), (1, 1), (-1, -1)] {
    assert_true(
      approx(
        @teich.m2_tr(@teich.eval_word(a, b, @teich.curve_word(p, q))),
        3.0,
        eps8,
      ),
    )
  }
}

///| The length spectrum of the modular torus: traces are 3 × Markoff numbers

///|
/// and lengths are realised by the trace formula tr = 2 cosh(l/2).
test "length spectrum of the modular torus" {
  let (a, b) = @teich.modular_torus()
  let spec = @teich.length_spectrum(a, b, 4)
  assert_true(spec.length() > 15)
  let mut shortest = 1000.0
  for i = 0; i < spec.length(); i = i + 1 {
    let (p, q, l) = spec[i]
    // primitive class
    assert_eq(@teich.gcd_i(p, q), 1)
    // length is positive and satisfies tr = 2 cosh(l/2)
    assert_true(l > 0.0)
    let t = @teich.m2_tr(@teich.eval_word(a, b, @teich.curve_word(p, q)))
    assert_true(approx(t, 2.0 * @math.cosh(l / 2.0), eps8))
    if l < shortest {
      shortest = l
    }
  }
  // the systole of the modular torus has length 2 arccosh(3/2)
  assert_true(approx(shortest, 2.0 * @math.acosh(1.5), eps6))
  // exactly three classes realise it: (1,0), (0,1), (1,1)
  let mut n_short = 0
  for i = 0; i < spec.length(); i = i + 1 {
    let (_p, _q, l) = spec[i]
    if approx(l, shortest, eps6) {
      n_short = n_short + 1
    }
  }
  assert_eq(n_short, 3)
}

///| Theorem (Fenchel–Nielsen).  The twist flow

///|        Φ_t (A,B) = ( A , A^{t/2} B A^{t/2} )

///| preserves tr A, the Markoff defect and the commutator trace, satisfies

///| the one-parameter group law Φ_{s+t} = Φ_s ∘ Φ_t, and the twist

///| coordinate τ adds: τ(Φ_t(X)) = τ(X) + t.  Hence

///|        T(S_{1,1}) ≅ R_{>0} × R ,   (l(A), τ · l(A))  are global

///|
/// coordinates, and along a twist orbit tr B is minimal exactly at τ = 0.
test "Fenchel-Nielsen twist flow: invariants, group law, twist coordinate" {
  let (a, b) = @teich.modular_torus()
  let x0 = @teich.m2_tr(a)
  let tau0 = @teich.twist_from_traces(
    x0,
    @teich.m2_tr(b),
    @teich.m2_tr(@teich.m2_mul(a, b)),
  )
  let mut previous_tau = tau0
  let mut previous_t = 0.0
  for t in [0.0, 0.25, 0.5, 1.0, 2.0, -0.7] {
    let (at, bt) = @teich.fn_twist(a, b, t)
    let xt = @teich.m2_tr(at)
    let yt = @teich.m2_tr(bt)
    let zt = @teich.m2_tr(@teich.m2_mul(at, bt))
    // stays in SL(2,R)
    assert_true(approx(@teich.m2_det(at), 1.0, eps8))
    assert_true(approx(@teich.m2_det(bt), 1.0, eps8))
    // tr A is the length coordinate: invariant
    assert_true(approx(xt, x0, eps8))
    // still a point of Teichmuller space: parabolic commutator, x²+y²+z²=xyz
    assert_true(approx(@teich.m2_tr(@teich.commutator(at, bt)), -2.0, eps7))
    assert_true(approx(@teich.markoff_defect(xt, yt, zt), 0.0, eps6))
    // the Fricke relation holds at the twisted point too
    assert_true(
      approx(
        @teich.fricke_commutator_trace(xt, yt, zt),
        @teich.m2_tr(@teich.commutator(at, bt)),
        eps6,
      ),
    )
    // the orbit invariant A_0 D_0 is constant along the flow
    assert_true(
      approx(
        @teich.twist_orbit_invariant(xt, yt, zt),
        @teich.twist_orbit_invariant(
          x0,
          @teich.m2_tr(b),
          @teich.m2_tr(@teich.m2_mul(a, b)),
        ),
        eps6,
      ),
    )
    // tau adds: tau(t) = tau(0) + t
    let tau_t = @teich.twist_from_traces(xt, yt, zt)
    assert_true(approx(tau_t - tau0, t, eps6))
    if t > previous_t {
      assert_true(tau_t > previous_tau)
    }
    previous_tau = tau_t
    previous_t = t
    // McShane still holds at the twisted point
    if t == 0.0 || t == 1.0 {
      assert_true(approx(@teich.mcshane_partial(at, bt, 6), 0.5, eps4))
    }
  }
  // group law: Phi_{s+t} = Phi_s o Phi_t  (checked on traces)
  let (a1, b1) = @teich.fn_twist(a, b, 0.3)
  let (a2, b2) = @teich.fn_twist(a1, b1, 0.4)
  let (a3, b3) = @teich.fn_twist(a, b, 0.7)
  assert_true(approx(@teich.m2_tr(b2), @teich.m2_tr(b3), eps8))
  assert_true(
    approx(
      @teich.m2_tr(@teich.m2_mul(a2, b2)),
      @teich.m2_tr(@teich.m2_mul(a3, b3)),
      eps8,
    ),
  )
  // tau = 0 is the point where tr B (hence l(B)) is minimal on the orbit
  let tau_min = 0.0 - tau0
  let (_am, bm) = @teich.fn_twist(a, b, tau_min)
  let y_min = @teich.m2_tr(bm)
  assert_true(
    approx(
      @teich.twist_from_traces(
        @teich.m2_tr(a),
        y_min,
        @teich.m2_tr(@teich.m2_mul(a, bm)),
      ),
      0.0,
      eps6,
    ),
  )
  for k = -6; k <= 6; k = k + 1 {
    let (_ak, bk) = @teich.fn_twist(a, b, tau_min + k.to_double() * 0.1)
    assert_true(@teich.m2_tr(bk) >= y_min - eps9)
  }
}
