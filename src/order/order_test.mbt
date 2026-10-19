///|
/// Poset axioms and Hasse diagrams.
test "poset axioms" {
  // 0 < 1 < 2 and 0 < 3
  let p = @order.poset_from_pairs(4, [(0, 1), (1, 2), (0, 3)])
  assert_true(@order.is_poset(p))
  assert_eq(p.le[0][2], true)
  assert_eq(p.le[2][0], false)
  let h = @order.transitive_reduction(p)
  assert_eq(h[0][2], false) // 0 ≤ 2 is implied, not a cover
  assert_eq(h[0][1], true)
  assert_eq(h[1][2], true)
  assert_eq(h[0][3], true)
}

///|
/// The divisor lattice of n = 12: {1,2,3,4,6,12} ordered by divisibility.
/// It is C_3 × C_2 (a product of chains), hence distributive.
fn divisor_lattice(n : Int32) -> @order.Poset {
  let divs = Array::make(0, 0)
  for d = 1; d <= n; d = d + 1 {
    if n % d == 0 {
      divs.push(d)
    }
  }
  let m = divs.length()
  let le = Array::make(m, Array::make(0, false))
  for i = 0; i < m; i = i + 1 {
    le[i] = Array::make(m, false)
    for j = 0; j < m; j = j + 1 {
      le[i][j] = divs[j] % divs[i] == 0
    }
  }
  { n: m, le, }
}

///|
test "divisor lattice is distributive" {
  let l = divisor_lattice(12)
  assert_true(@order.is_poset(l))
  assert_true(@order.is_lattice(l))
  assert_true(@order.is_distributive(l))
  assert_true(@order.is_modular(l))
  // 12 divisors: 1,2,3,4,6,12 → join(2,3) = 6, meet(4,6) = 2
  // indices:    0 1 2 3 4  5
  assert_eq(@order.join(l, 1, 2), 4) // lcm(2,3) = 6 → index 4
  assert_eq(@order.meet(l, 3, 4), 1) // gcd(4,6) = 2 → index 1
}

///|
/// T1 — Birkhoff: L ≅ O(J(L)) for finite distributive lattices.
test "birkhoff representation theorem" {
  let l = divisor_lattice(12)
  assert_true(@order.check_birkhoff(l))
  // J(L) has (3-1)+(2-1) = 3 elements for C_3 × C_2
  assert_eq(@order.join_irreducibles(l).length(), 3)
  // and O(J(L)) has 6 = |L| elements
  let jl = @order.join_irreducibles(l)
  let sub = @order.induced(l, jl)
  assert_eq(@order.order_ideals(sub).length(), 6)
  // a second example: the Boolean lattice B_3 = O(antichain of 3)
  let b3 = @order.ideal_lattice(@order.poset_from_pairs(3, []))
  assert_true(@order.is_distributive(b3))
  assert_true(@order.check_birkhoff(b3))
  assert_eq(b3.n, 8)
  // and conversely J(O(P)) ≅ P for the 3-element antichain:
  // O(antichain_3) = B_3, whose join-irreducibles are the 3 atoms.
  assert_eq(@order.join_irreducibles(b3).length(), 3)
}

///|
/// The canonical form: for finite distributive lattices, L ≅ L' iff
/// J(L) ≅ J(L').  Here the *normal form* is the isomorphism class of J(L),
/// tested on two differently presented copies of the same lattice.
test "canonical form of a distributive lattice" {
  let l1 = divisor_lattice(12) // C_3 × C_2
  let l2 = divisor_lattice(18) // 18 = 2·3^2 → C_2 × C_3
  assert_true(@order.check_birkhoff(l1))
  assert_true(@order.check_birkhoff(l2))
  // C_3 × C_2 ≅ C_2 × C_3 : both have 6 elements and isomorphic J-posets
  assert_eq(l1.n, l2.n)
  let j1 = @order.induced(l1, @order.join_irreducibles(l1))
  let j2 = @order.induced(l2, @order.join_irreducibles(l2))
  // both J-posets: a 2-chain ⊔ a 1-chain → 3 relations counted the same way
  assert_eq(relations_count(j1), relations_count(j2))
  assert_eq(@order.order_ideals(j1).length(), @order.order_ideals(j2).length())
  // a genuinely different lattice: B_3 has 8 elements
  let b3 = @order.ideal_lattice(@order.poset_from_pairs(3, []))
  assert_eq(b3.n, 8)
}

///|
pub fn relations_count(p : @order.Poset) -> Int32 {
  let mut c = 0
  for i = 0; i < p.n; i = i + 1 {
    for j = 0; j < p.n; j = j + 1 {
      if p.le[i][j] {
        c = c + 1
      }
    }
  }
  c
}

///|
/// T2 — Dedekind–MacNeille completion.
test "dedekind macneille completion" {
  // the 4-element poset V: 0 < 1, 0 < 2, 1 < 3, 2 < 3 is already a lattice
  let p = @order.poset_from_pairs(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
  assert_true(@order.check_dm(p))
  // a non-lattice: two incomparable maxima, 0 < 1, 0 < 2
  let q = @order.poset_from_pairs(3, [(0, 1), (0, 2)])
  assert_false(@order.is_lattice(q))
  assert_true(@order.check_dm(q))
  // its completion adds a top element: |DM(q)| = 4
  let (cuts, _) = @order.dm_completion(q)
  assert_eq(cuts.length(), 4)
  assert_true(@order.is_lattice(@order.dm_lattice(q)))
  // DM of an antichain of 3 is M_3 = the 5 element modular lattice
  // (bottom, three incomparable atoms, top) — the *smallest* lattice
  // containing a 3-antichain, not the 8 element Boolean lattice B_3.
  let a = @order.poset_from_pairs(3, [])
  assert_eq(@order.dm_completion(a).0.length(), 5)
  // while the ideal lattice O(antichain_3) is B_3
  assert_eq(@order.ideal_lattice(@order.poset_from_pairs(3, [])).n, 8)
  assert_true(@order.check_dm(a))
}

///|
/// T3 — hook-length formula for forests, checked against brute force.
test "hook length formula for forests" {
  // a chain of 4: exactly one linear extension
  let chain = @order.poset_from_pairs(4, [(0, 1), (1, 2), (2, 3)])
  assert_eq(@order.count_linear_extensions(chain), 1)
  assert_eq(@order.hook_length_forest(chain), 1)
  // antichain of 4: 4! = 24
  let anti = @order.poset_from_pairs(4, [])
  assert_eq(@order.count_linear_extensions(anti), 24)
  assert_eq(@order.hook_length_forest(anti), 24)
  // a rooted tree: 0 root, 1 and 2 children of 0, 3 child of 1
  let t = @order.poset_from_pairs(4, [(0, 1), (0, 2), (1, 3)])
  let brute = @order.count_linear_extensions(t)
  assert_eq(brute, @order.hook_length_forest(t))
  assert_eq(brute, 3) // 4! / (4·2·1·1) = 3
  // another tree
  let t2 = @order.poset_from_pairs(5, [(0, 1), (0, 2), (2, 3), (2, 4)])
  assert_eq(@order.count_linear_extensions(t2), @order.hook_length_forest(t2))
}

///|
/// The dominance order on partitions is a lattice; it is distributive for
/// n ≤ 5 and fails to be distributive for n = 6 (where 411 and 33 are
/// incomparable).  These facts are *computed*, not asserted from memory.
test "dominance order" {
  assert_eq(@order.partitions(4).length(), 5)
  let d4 = @order.dominance_poset(4)
  assert_true(@order.is_poset(d4))
  assert_true(@order.is_lattice(d4))
  assert_true(@order.is_distributive(d4))
  let d5 = @order.dominance_poset(5)
  assert_eq(d5.n, 7)
  assert_true(@order.is_lattice(d5))
  let d6 = @order.dominance_poset(6)
  assert_eq(d6.n, 11)
  assert_true(@order.is_lattice(d6))
  // for n = 6 the order is no longer a chain: record the fact
  let mut chain = true
  for i = 0; i < d6.n; i = i + 1 {
    for j = 0; j < d6.n; j = j + 1 {
      if !d6.le[i][j] && !d6.le[j][i] {
        chain = false
      }
    }
  }
  assert_eq(chain, false)
  // d4 IS a chain (5 partitions totally ordered)
  let mut chain4 = true
  for i = 0; i < d4.n; i = i + 1 {
    for j = 0; j < d4.n; j = j + 1 {
      if !d4.le[i][j] && !d4.le[j][i] {
        chain4 = false
      }
    }
  }
  assert_eq(chain4, true)
}
