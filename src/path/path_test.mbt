///|
/// Compile-time endpoint typing: composition only type checks when the
/// endpoints match.  (Writing `compose(p, q)` with mismatched endpoints is a
/// compile error, not a runtime one.)
test "typed composition in the free category" {
  let e01 : @path.Edge[@path.V0, @path.V1] = @path.edge(10, 0, 1)
  let e12 : @path.Edge[@path.V1, @path.V2] = @path.edge(11, 1, 2)
  let e23 : @path.Edge[@path.V2, @path.V3] = @path.edge(12, 2, 3)
  let p01 : @path.Path[@path.V0, @path.V1] = @path.cons(e01, @path.nil())
  let p12 : @path.Path[@path.V1, @path.V2] = @path.cons(e12, @path.nil())
  let p02 = @path.compose(p01, p12)
  assert_eq(p02.steps, [10, 11])
  let p23 : @path.Path[@path.V2, @path.V3] = @path.cons(e23, @path.nil())
  assert_eq(@path.compose(p02, p23).steps, [10, 11, 12])
  // associativity of composition, as a runtime identity
  let lhs = @path.compose(@path.compose(p01, p12), p23)
  let rhs = @path.compose(p01, @path.compose(p12, p23))
  assert_eq(lhs.steps, rhs.steps)
  // units
  assert_eq(@path.compose(p01, @path.nil()).steps, p01.steps)
  assert_eq(@path.compose(@path.nil(), p01).steps, p01.steps)
  assert_eq(@path.length(p02), 2)
}

///|
/// Length-indexed paths: the index is checked against the runtime length by
/// `llength_certified` (which aborts on disagreement — it never does in the
/// tests below because the index is built by the type rules).
test "length indexed paths" {
  let e01 : @path.Edge[@path.V0, @path.V1] = @path.edge(10, 0, 1)
  let e12 : @path.Edge[@path.V1, @path.V2] = @path.edge(11, 1, 2)
  let e23 : @path.Edge[@path.V2, @path.V3] = @path.edge(12, 2, 3)
  let a : @path.LPath[@tl.S[@tl.Z], @path.V0, @path.V1] = @path.lcons(e01, @path.lnil())
  let b : @path.LPath[@tl.S[@tl.Z], @path.V1, @path.V2] = @path.lcons(e12, @path.lnil())
  let c : @path.LPath[@tl.S[@tl.Z], @path.V2, @path.V3] = @path.lcons(e23, @path.lnil())
  // lcompose returns LPath[Plus[N,M], A, C]: the length index is *added*
  // by the type system, and `llength_certified` reifies it (at compile
  // time) and cross-checks it against the runtime array.
  let ab = @path.lcompose(a, b)
  assert_eq(ab.steps, [10, 11])
  let abc = @path.lcompose(ab, c)
  assert_eq(abc.steps, [10, 11, 12])
  assert_eq(@path.llength_certified(a), 1)
  assert_eq(@path.llength_certified(ab), 2)
  assert_eq(@path.llength_certified(abc), 3)
  // the certified length of a composite equals the sum of the certified ones
  assert_eq(
    @path.llength_certified(abc),
    @path.llength_certified(a) + @path.llength_certified(b) + @path.llength_certified(c),
  )
}

///|
/// T1 — reduction in the free groupoid is confluent, so the reduced word is
/// the canonical representative: 同構即相同.
test "word reduction is confluent" {
  // a a^-1 -> empty
  assert_eq(@path.reduce([3, @path.invert_letter(3)]), [])
  assert_eq(@path.reduce([3, @path.invert_letter(3), 3]), [3])
  // exhaustive confluence check on all short words over 2 letters
  let mut seed = 12345
  for t = 0; t < 60; t = t + 1 {
    seed = (seed * 1103515245 + 12345) % 1000003
    let n = 4 + seed % 4
    let w : Array[Int32] = Array::make(0, 0)
    for i = 0; i < n; i = i + 1 {
      seed = (seed * 1103515245 + 12345) % 1000003
      let a = seed % 2
      w.push(if seed % 3 == 0 { @path.invert_letter(a) } else { a })
    }
    assert_true(@path.confluent(w))
    // reducing twice is the same as reducing once (idempotence)
    assert_true(@path.word_eq(@path.reduce(@path.reduce(w)), @path.reduce(w)))
    // p ~ q iff NF(p) = NF(q)
    assert_true(@path.homotopic_rel_endpoints(w, @path.reduce(w)))
  }
  // a word that is not reduced, with several possible first moves
  let w = [0, @path.invert_letter(0), 1, @path.invert_letter(1), 0]
  assert_true(@path.confluent(w))
  assert_eq(@path.reduce(w), [0])
}

///|
/// T2 — π₁ of a connected graph is free of rank |E| − |V| + 1, and the
/// spanning-tree generators give an isomorphism F_r → π₁(Γ, v₀): the map
/// from reduced words to reduced loops is injective.
test "pi1 of a graph" {
  // theta graph: two vertices joined by three edges → rank 2
  let g = @path.graph_make(2, [(0, 1), (0, 1), (0, 1)])
  let (r, gens) = @path.fundamental_group(g, 0)
  assert_eq(r, 2)
  assert_eq(gens.length(), 2)
  assert_true(injective_on_ball(gens, 2, 3))
  // a triangle (3 vertices, 3 edges) → rank 1
  let g2 = @path.graph_make(3, [(0, 1), (1, 2), (2, 0)])
  let (r2, gens2) = @path.fundamental_group(g2, 0)
  assert_eq(r2, 1)
  assert_eq(gens2.length(), 1)
  assert_true(injective_on_ball(gens2, 1, 4))
  // a tree has trivial π₁
  let g3 = @path.graph_make(4, [(0, 1), (1, 2), (1, 3)])
  let (r3, gens3) = @path.fundamental_group(g3, 0)
  assert_eq(r3, 0)
  assert_eq(gens3.length(), 0)
  // figure eight: one vertex, two loops → rank 2
  let g4 = @path.graph_make(1, [(0, 0), (0, 0)])
  let (r4, _) = @path.fundamental_group(g4, 0)
  assert_eq(r4, 2)
  // rank formula against the spanning-tree count
  assert_eq(@path.count_components(@path.graph_make(5, [(0, 1), (2, 3)])), 3)
}

///|
/// Check that w ↦ [w] is injective on the ball of radius `maxlen` in F_r.
fn injective_on_ball(gens : Array[@path.Word], r : Int32, maxlen : Int32) -> Bool {
  let words = @path.reduced_words(r, maxlen)
  let images : Array[@path.Word] = Array::make(0, Array::make(0, 0))
  for w in words {
    images.push(@path.eval_word(gens, w))
  }
  for i = 0; i < words.length(); i = i + 1 {
    for j = i + 1; j < words.length(); j = j + 1 {
      if @path.word_eq(images[i], images[j]) {
        return false
      }
    }
  }
  true
}

///|
/// The growth of the free group: |ball of radius k| = 1 + Σ_{i≤k} 2r(2r−1)^{i−1}.
test "free group growth" {
  assert_eq(@path.reduced_words(2, 3).length(), @path.free_group_ball_size(2, 3))
  assert_eq(@path.reduced_words(1, 4).length(), @path.free_group_ball_size(1, 4))
  assert_eq(@path.free_group_ball_size(2, 1), 1 + 4)
  assert_eq(@path.free_group_ball_size(2, 2), 1 + 4 + 12)
  assert_eq(@path.reduced_words(3, 2).length(), @path.free_group_ball_size(3, 2))
}

///|
/// The path algebra: multiplication is concatenation when endpoints match,
/// zero otherwise, and it is graded by length.
test "path algebra" {
  let p : @path.PathElem = { src: 0, dst: 1, edges: [0], }
  let q : @path.PathElem = { src: 1, dst: 2, edges: [1], }
  let bad : @path.PathElem = { src: 5, dst: 2, edges: [1], }
  let pq = @path.path_mul(p, q)
  assert_true(pq is Some(_))
  match pq {
    Some(x) => {
      assert_eq(x.src, 0)
      assert_eq(x.dst, 2)
      assert_eq(x.edges, [0, 1])
      assert_eq(@path.path_degree(x), @path.path_degree(p) + @path.path_degree(q))
    }
    None => assert_true(false)
  }
  assert_true(@path.path_mul(p, bad) is None)
  // associativity
  let r : @path.PathElem = { src: 2, dst: 3, edges: [2], }
  let lhs = @path.path_mul(@path.path_mul(p, q).unwrap(), r)
  let rhs = @path.path_mul(p, @path.path_mul(q, r).unwrap())
  assert_eq(lhs.unwrap().edges, [0, 1, 2])
  assert_eq(rhs.unwrap().edges, [0, 1, 2])
}
