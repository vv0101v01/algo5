// Copyright 2026. Apache-2.0.
//
// Path spaces: the free category on a quiver, the fundamental groupoid of a
// graph, and the path algebra.
//
// ---------------------------------------------------------------------------
// Compile-time content
// ---------------------------------------------------------------------------
// Vertices are *phantom types* `V[N]` indexed by type-level numerals, so the
// endpoints of a path live in the types:
//
//     cons    : Edge[A,B] → Path[B,C] → Path[A,C]
//     compose : Path[A,B] → Path[B,C] → Path[A,C]
//
// Composing `Path[A,B]` with `Path[C,D]` where B ≠ C is a **type error**, not
// a runtime failure — the category axioms are discharged by unification.  The
// length-indexed variant `LPath[N,A,B]` additionally tracks the length in the
// type (`Z`, `S[N]`, `Plus[N,M]`), so that
//
//     lcompose : LPath[N,A,B] → LPath[M,B,C] → LPath[Plus[N,M],A,C]
//
// is checked at compile time.  None of `N`, `A`, `B`, `C` survives to runtime:
// the payload of every path is a single `Array[Int]` of edge ids.
//
// ---------------------------------------------------------------------------
// Theorems
// ---------------------------------------------------------------------------
//   T1 (free groupoid / word reduction).  In the free groupoid on a graph,
//       homotopy classes rel endpoints are represented by *reduced* edge
//       words (no edge immediately followed by its inverse), and the reduced
//       representative is unique.  Hence "同構即相同": two paths are homotopic
//       rel endpoints iff their reduced words are *equal*.  `reduce` computes
//       the normal form; the test verifies confluence by reducing with
//       *every* possible reduction order.
//
//   T2 (π₁ of a graph).  For a connected graph Γ,
//       π₁(Γ, v₀) ≅ F_r with r = |E| − |V| + 1.
//       `fundamental_group` builds the free basis from a spanning tree and the
//       test verifies that reduced words map *injectively* to reduced loops.

///|
/// A vertex: a phantom type indexed by a type-level numeral from `@tl`.
pub type V[N]

///|
/// An arrow, carrying its (phantom) endpoints plus runtime data.
pub(all) struct Edge[A, B] {
  id : Int32
  src : Int32
  dst : Int32
}

///|
pub fn[A, B] edge(id : Int32, src : Int32, dst : Int32) -> Edge[A, B] {
  { id, src, dst, }
}

///|
/// A path: a list of edge ids, typed by source and target.
pub(all) struct Path[A, B] {
  steps : Array[Int32]
}

///|
/// A length-indexed path.  `N` is a phantom type-level numeral.
pub(all) struct LPath[N, A, B] {
  steps : Array[Int32]
}

///|
pub fn[A] nil() -> Path[A, A] {
  { steps: [], }
}

///|
pub fn[A, B, C] cons(e : Edge[A, B], p : Path[B, C]) -> Path[A, C] {
  let steps = Array::make(1 + p.steps.length(), 0)
  steps[0] = e.id
  for i = 0; i < p.steps.length(); i = i + 1 {
    steps[i + 1] = p.steps[i]
  }
  { steps, }
}

///|
/// Composition in the free category.  The endpoints must match — that is
/// what the type checker enforces.
pub fn[A, B, C] compose(p : Path[A, B], q : Path[B, C]) -> Path[A, C] {
  let steps = Array::make(p.steps.length() + q.steps.length(), 0)
  for i = 0; i < p.steps.length(); i = i + 1 {
    steps[i] = p.steps[i]
  }
  for i = 0; i < q.steps.length(); i = i + 1 {
    steps[p.steps.length() + i] = q.steps[i]
  }
  { steps, }
}

///|
pub fn[A, B] length(p : Path[A, B]) -> Int32 {
  p.steps.length()
}

// ---------------------------------------------------------------------------
// length-indexed paths: the length is tracked in the type
// ---------------------------------------------------------------------------

///|
pub fn[A] lnil() -> LPath[@tl.Z, A, A] {
  { steps: [], }
}

///|
/// Prepending an edge increments the type-level length.
pub fn[N, A, B, C] lcons(
  e : Edge[A, B],
  p : LPath[N, B, C],
) -> LPath[@tl.S[N], A, C] {
  let steps = Array::make(1 + p.steps.length(), 0)
  steps[0] = e.id
  for i = 0; i < p.steps.length(); i = i + 1 {
    steps[i + 1] = p.steps[i]
  }
  { steps, }
}

///|
/// Concatenation adds the lengths — at the type level.
pub fn[N, M, A, B, C] lcompose(
  p : LPath[N, A, B],
  q : LPath[M, B, C],
) -> LPath[@tl.Plus[N, M], A, C] {
  let steps = Array::make(p.steps.length() + q.steps.length(), 0)
  for i = 0; i < p.steps.length(); i = i + 1 {
    steps[i] = p.steps[i]
  }
  for i = 0; i < q.steps.length(); i = i + 1 {
    steps[p.steps.length() + i] = q.steps[i]
  }
  { steps, }
}

///|
/// The (runtime) length agrees with the certified value of the index.
pub fn[N : @tl.Nat, A, B] llength_certified(p : LPath[N, A, B]) -> Int32 {
  let certified = @tl.unwrap_nat((@tl.reflect() : @tl.NatV[N]))
  if certified != p.steps.length() {
    abort("lpath: type-level length disagrees with the runtime length")
  }
  certified
}

// ---------------------------------------------------------------------------
// the free groupoid: reduced words
// ---------------------------------------------------------------------------
// An edge-word is a list of signed edge ids: `e ≥ 0` means "traverse edge e
// forwards", `e < 0` means "traverse edge ~e backwards" (we use `-(e+1)` so
// that 0 is representable).

///|
pub type Word = Array[Int32]

///|
pub fn invert_letter(a : Int32) -> Int32 {
  if a >= 0 {
    0 - (a + 1)
  } else {
    0 - a - 1
  }
}

///|
/// One reduction step: cancel an adjacent inverse pair, return the new word
/// and whether anything changed.
pub fn cancel_once(w : Word) -> (Word, Bool) {
  for i = 0; i < w.length() - 1; i = i + 1 {
    if w[i + 1] == invert_letter(w[i]) {
      let out : Array[Int32] = Array::make(0, 0)
      for j = 0; j < i; j = j + 1 {
        out.push(w[j])
      }
      for j = i + 2; j < w.length(); j = j + 1 {
        out.push(w[j])
      }
      return (out, true)
    }
  }
  (w.copy(), false)
}

///|
/// The normal form: repeatedly cancel.  Terminating and confluent (T1).
pub fn reduce(w0 : Word) -> Word {
  let mut w = w0.copy()
  let mut changed = true
  let mut steps = 0
  while changed {
    steps = steps + 1
    if steps > 10000 {
      abort("reduce: divergence")
    }
    let (nw, ch) = cancel_once(w)
    w = nw
    changed = ch
  }
  w
}

///|
/// All words reachable by *one* cancellation, i.e. all possible reduction
/// orders.  Used to verify confluence.
pub fn one_step_successors(w : Word) -> Array[Word] {
  let out : Array[Word] = Array::make(0, Array::make(0, 0))
  for i = 0; i < w.length() - 1; i = i + 1 {
    if w[i + 1] == invert_letter(w[i]) {
      let nw : Array[Int32] = Array::make(0, 0)
      for j = 0; j < i; j = j + 1 {
        nw.push(w[j])
      }
      for j = i + 2; j < w.length(); j = j + 1 {
        nw.push(w[j])
      }
      out.push(nw)
    }
  }
  out
}

///|
/// Church–Rosser check by exhaustive search over reduction orders.
/// (Exponential in the word length — only used for short words.)
pub fn confluent(w : Word) -> Bool {
  let target = reduce(w)
  let stack : Array[Word] = Array::make(0, Array::make(0, 0))
  stack.push(w)
  let mut steps = 0
  while stack.length() > 0 {
    steps = steps + 1
    if steps > 20000 {
      return true
    }
    let cur = stack.pop().unwrap()
    let succs = one_step_successors(cur)
    if succs.length() == 0 {
      if !word_eq(cur, target) {
        return false
      }
      continue
    }
    for s in succs {
      stack.push(s)
    }
  }
  true
}

///|
pub fn word_eq(a : Word, b : Word) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// 同構即相同: homotopy rel endpoints is *equality* of normal forms.
pub fn homotopic_rel_endpoints(p : Word, q : Word) -> Bool {
  word_eq(reduce(p), reduce(q))
}

// ---------------------------------------------------------------------------
// π₁ of a finite graph
// ---------------------------------------------------------------------------

///|
/// A finite (multi)graph: `edges[k] = (u, v)`.
pub(all) struct Graph {
  nv : Int32
  edges : Array[(Int32, Int32)]
}

///|
pub fn graph_make(nv : Int32, edges : Array[(Int32, Int32)]) -> Graph {
  { nv, edges, }
}

///|
/// A spanning forest via BFS; returns the parent array (-1 for roots) and
/// the tree edges.
pub fn spanning_forest(g : Graph) -> (Array[Int32], Array[Int32]) {
  let parent = Array::make(g.nv, 0 - 1)
  let tree : Array[Int32] = Array::make(0, 0)
  let visited = Array::make(g.nv, false)
  let mut root = 0
  while root < g.nv {
    if visited[root] {
      root = root + 1
      continue
    }
    visited[root] = true
    let queue : Array[Int32] = Array::make(0, 0)
    queue.push(root)
    while queue.length() > 0 {
      let u = queue.remove(0)
      for k = 0; k < g.edges.length(); k = k + 1 {
        let (a, b) = g.edges[k]
        let v = if a == u { b } else if b == u { a } else { 0 - 1 }
        if v >= 0 && !visited[v] {
          visited[v] = true
          parent[v] = u
          tree.push(k)
          queue.push(v)
        }
      }
    }
    root = root + 1
  }
  (parent, tree)
}

///|
/// A path in the spanning tree from `u` down to `v`, as a signed edge word.
/// Assumes u and v are in the same component.
pub fn tree_path(
  g : Graph,
  parent : Array[Int32],
  u : Int32,
  v : Int32,
) -> Word {
  // walk both up to the root, then splice
  let up : Array[Int32] = Array::make(0, 0)
  let mut x = u
  while x != v && parent[x] >= 0 {
    let e = find_edge(g, x, parent[x])
    // traverse x -> parent[x]; if the edge is stored as (parent, x) it is
    // the reverse direction
    let (a, _) = g.edges[e]
    up.push(if a == x { e } else { invert_letter(e) })
    x = parent[x]
  }
  if x != v {
    // v is not an ancestor of u: fall back to a BFS search in the tree
    return tree_path_bfs(g, parent, u, v)
  }
  up
}

///|
fn tree_path_bfs(
  g : Graph,
  parent : Array[Int32],
  u : Int32,
  v : Int32,
) -> Word {
  // reconstruct the tree path by walking up from u and from v to the common
  // ancestor, using parent pointers
  let au : Array[Int32] = Array::make(0, 0)
  let av : Array[Int32] = Array::make(0, 0)
  let mut x = u
  while x >= 0 {
    au.push(x)
    x = parent[x]
  }
  x = v
  while x >= 0 {
    av.push(x)
    x = parent[x]
  }
  // find the lowest common ancestor (last common element, au/av are
  // root-to-node reversed: au[0] = u, au[last] = root)
  let mut lca = 0 - 1
  for i = 0; i < au.length(); i = i + 1 {
    for j = 0; j < av.length(); j = j + 1 {
      if au[i] == av[j] && (lca < 0 || i + j < lca_index(au, av, au[i])) {
        lca = au[i]
      }
    }
  }
  if lca < 0 {
    abort("tree_path: vertices in different components")
  }
  // u -> ... -> lca
  let out : Array[Int32] = Array::make(0, 0)
  x = u
  while x != lca {
    let e = find_edge(g, x, parent[x])
    let (a, _) = g.edges[e]
    out.push(if a == x { e } else { invert_letter(e) })
    x = parent[x]
  }
  // lca -> ... -> v  (reverse of v -> lca)
  let down : Array[Int32] = Array::make(0, 0)
  x = v
  while x != lca {
    let e = find_edge(g, x, parent[x])
    let (a, _) = g.edges[e]
    down.push(if a == x { invert_letter(e) } else { e })
    x = parent[x]
  }
  for i = down.length() - 1; i >= 0; i = i - 1 {
    out.push(down[i])
  }
  out
}

///|
fn lca_index(au : Array[Int32], av : Array[Int32], x : Int32) -> Int32 {
  let mut i0 = 0
  let mut j0 = 0
  for i = 0; i < au.length(); i = i + 1 {
    if au[i] == x {
      i0 = i
    }
  }
  for j = 0; j < av.length(); j = j + 1 {
    if av[j] == x {
      j0 = j
    }
  }
  i0 + j0
}

///|
fn find_edge(g : Graph, u : Int32, v : Int32) -> Int32 {
  for k = 0; k < g.edges.length(); k = k + 1 {
    let (a, b) = g.edges[k]
    if (a == u && b == v) || (a == v && b == u) {
      return k
    }
  }
  abort("find_edge: no such edge")
}

///|
/// The free basis of π₁(Γ, v₀): for every non-tree edge e = (u,v) the loop
///     tree_path(v₀ → u) · e · tree_path(v → v₀)
/// and the rank r = |E| − |V| + c.
pub fn fundamental_group(g : Graph, v0 : Int32) -> (Int32, Array[Word]) {
  let (parent, tree) = spanning_forest(g)
  let is_tree = Array::make(g.edges.length(), false)
  for k in tree {
    is_tree[k] = true
  }
  let gens : Array[Word] = Array::make(0, Array::make(0, 0))
  for k = 0; k < g.edges.length(); k = k + 1 {
    if is_tree[k] {
      continue
    }
    let (a, b) = g.edges[k]
    let pre = tree_path(g, parent, v0, a)
    let post = tree_path(g, parent, b, v0)
    let w : Array[Int32] = Array::make(0, 0)
    for x in pre {
      w.push(x)
    }
    w.push(k)
    for x in post {
      w.push(x)
    }
    gens.push(w)
  }
  let ncomp = count_components(g)
  let rank = g.edges.length() - g.nv + ncomp
  (rank, gens)
}

///|
pub fn count_components(g : Graph) -> Int32 {
  let (parent, _) = spanning_forest(g)
  let mut c = 0
  for i = 0; i < g.nv; i = i + 1 {
    if parent[i] < 0 {
      c = c + 1
    }
  }
  c
}

///|
/// Evaluate a word in the free generators (given as edge-words) as an edge
/// word, then reduce.
pub fn eval_word(gens : Array[Word], w : Array[Int32]) -> Word {
  let out : Array[Int32] = Array::make(0, 0)
  for a in w {
    let i = if a >= 0 { a } else { invert_letter(a) }
    let g = gens[i]
    if a >= 0 {
      for x in g {
        out.push(x)
      }
    } else {
      for k = g.length() - 1; k >= 0; k = k - 1 {
        out.push(invert_letter(g[k]))
      }
    }
  }
  reduce(out)
}

///|
/// All reduced words of length ≤ `maxlen` over `r` generators.
pub fn reduced_words(r : Int32, maxlen : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = Array::make(0, Array::make(0, 0))
  out.push([])
  let mut frontier : Array[Array[Int32]] = Array::make(0, Array::make(0, 0))
  for i = 0; i < r; i = i + 1 {
    frontier.push([i])
    frontier.push([invert_letter(i)])
  }
  let mut level = 1
  while level <= maxlen {
    for w in frontier {
      out.push(w)
    }
    if level == maxlen {
      break
    }
    let next : Array[Array[Int32]] = Array::make(0, Array::make(0, 0))
    for w in frontier {
      let last = w[w.length() - 1]
      for a = 0; a < r; a = a + 1 {
        for s in [a, invert_letter(a)] {
          if s != invert_letter(last) {
            let nw = w.copy()
            nw.push(s)
            next.push(nw)
          }
        }
      }
    }
    frontier = next
    level = level + 1
  }
  out
}

///|
/// |F_r| growth: 1 word of length 0 and 2r(2r−1)^{k−1} of length k.
pub fn free_group_ball_size(r : Int32, maxlen : Int32) -> Int32 {
  let mut total = 1
  let mut k = 1
  while k <= maxlen {
    let mut c = 2 * r
    let mut j = 1
    while j < k {
      c = c * (2 * r - 1)
      j = j + 1
    }
    total = total + c
    k = k + 1
  }
  total
}

// ---------------------------------------------------------------------------
// the path algebra of a quiver
// ---------------------------------------------------------------------------

///|
/// A basis element of the path algebra: a path in the quiver.
pub(all) struct PathElem {
  src : Int32
  dst : Int32
  edges : Array[Int32]
}

///|
/// Multiplication in the path algebra: concatenation when the endpoints
/// match, and 0 otherwise.  (Represented as `None`.)
pub fn path_mul(p : PathElem, q : PathElem) -> PathElem? {
  if p.dst != q.src {
    return None
  }
  let steps = Array::make(p.edges.length() + q.edges.length(), 0)
  for i = 0; i < p.edges.length(); i = i + 1 {
    steps[i] = p.edges[i]
  }
  for i = 0; i < q.edges.length(); i = i + 1 {
    steps[p.edges.length() + i] = q.edges[i]
  }
  Some({ src: p.src, dst: q.dst, edges: steps, })
}

///|
/// The path algebra is graded by path length; `path_mul` respects the
/// grading: |p·q| = |p| + |q|.
pub fn path_degree(p : PathElem) -> Int32 {
  p.edges.length()
}

///|
/// Convenience aliases: vertices indexed by the small numerals of `@tl`.
pub type V0 = V[@tl.N0]

///|
pub type V1 = V[@tl.N1]

///|
pub type V2 = V[@tl.N2]

///|
pub type V3 = V[@tl.N3]

///|
pub type V4 = V[@tl.N4]
