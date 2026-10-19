///|
/// LLL terminates, returns a reduced basis of the *same* lattice, and
/// preserves the determinant.
test "lll reduction certificates" {
  let b = [[1, 1], [1, 2]]
  let r = @lat.lll_reduce(b, 0.75)
  assert_true(@lat.is_lll_reduced(r, 0.75, 1.0e-9))
  assert_true(@lat.same_lattice(b, r))
  assert_eq(@lat.lattice_det(b), @lat.lattice_det(r))
  // the classic 3-dimensional example from the literature
  let c = [[1, 1, 1], [0 - 1, 0, 2], [3, 5, 6]]
  let rc = @lat.lll_reduce(c, 0.99)
  assert_true(@lat.is_lll_reduced(rc, 0.99, 1.0e-9))
  assert_true(@lat.same_lattice(c, rc))
  assert_eq(@lat.lattice_det(c), @lat.lattice_det(rc))
  // a badly skewed basis in dimension 4
  let d = [[1, 0, 0, 0], [12345, 1, 0, 0], [0, 6789, 1, 0], [0, 0, 1357, 1]]
  let rd = @lat.lll_reduce(d, 0.75)
  assert_true(@lat.is_lll_reduced(rd, 0.75, 1.0e-6))
  assert_true(@lat.same_lattice(d, rd))
  assert_eq(@lat.lattice_det(d), 1)
  assert_eq(@lat.lattice_det(rd), 1)
}

///|
/// LLL actually shortens the basis: the first vector is at most
/// 2^{(n-1)/2} times the shortest vector, verified against brute force.
test "lll finds a short vector" {
  let b = [[12, 3], [7, 2]]
  let r = @lat.lll_reduce(b, 0.99)
  let shortest = @lat.shortest_norm2_brute(b, 6)
  let first = @lat.norm2(r[0])
  assert_true(first <= @lat.lll_approximation_factor(2) * shortest + 1.0e-9)
  // and the first vector really is a lattice vector: adding it to the basis
  // does not change the lattice
  assert_true(@lat.same_lattice(b, [r[0], r[1]]))
  // 3-dimensional check
  let c = [[1, 1, 1], [0 - 1, 0, 2], [3, 5, 6]]
  let rc = @lat.lll_reduce(c, 0.99)
  let sc = @lat.shortest_norm2_brute(c, 4)
  assert_true(@lat.norm2(rc[0]) <= @lat.lll_approximation_factor(3) * sc + 1.0e-9)
}

///|
/// 同構即相同: equality of sublattices of Z^m is decided by equality of
/// Hermite normal forms.
test "lattice equality = equality of normal forms" {
  let a = [[2, 0], [0, 2]]
  let b = [[2, 0], [2, 2]]
  assert_true(@lat.same_lattice(a, b))
  let c = [[2, 0], [0, 4]]
  assert_false(@lat.same_lattice(a, c))
  // index: det(HNF(a)) / det(HNF(c)) = 4/8
  assert_eq(@nf.mat_det(@nf.hermite_normal_form(a)), 4)
  assert_eq(@nf.mat_det(@nf.hermite_normal_form(c)), 8)
  // a rank-deficient pair: both generate 2Z × {0}
  assert_true(@lat.same_lattice([[2, 0], [4, 0]], [[2, 0], [0 - 2, 0]]))
}

///|
/// Gram matrix and Hadamard's bound.
test "gram and hadamard" {
  let b = [[1, 1, 0], [0, 1, 1]]
  let g = @lat.gram(b)
  assert_eq(g[0][0], 2)
  assert_eq(g[0][1], 1)
  assert_eq(g[1][1], 2)
  let d = [[3, 0], [0, 4]]
  let hb = @lat.hadamard_bound(d)
  assert_true(hb >= 12.0 - 1.0e-9)
  assert_eq(@lat.lattice_det(d), 12)
}
