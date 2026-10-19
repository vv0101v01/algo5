///|
/// Structural predicates: `Nat`, `Even`, `Odd`, `Pos` are decided by the
/// trait solver while type checking.
fn[N : @tl.Nat, A] nat_guarded(v : @tl.Vec[N, A]) -> Int32 {
  // the bound is what makes the certificate available at all
  let _c = (@tl.Nat::cert(()) : @tl.NatV[N])
  v.data.length()
}

///|
fn[N : @tl.Even, A] even_guarded(v : @tl.Vec[N, A]) -> Int32 {
  // the bound is what makes the certificate available at all
  let _c = (@tl.Even::even_cert(()) : @tl.Flag[N])
  v.data.length()
}

///|
fn[N : @tl.Odd, A] odd_guarded(v : @tl.Vec[N, A]) -> Int32 {
  // the bound is what makes the certificate available at all
  let _c = (@tl.Odd::odd_cert(()) : @tl.Flag[N])
  v.data.length()
}

///|
fn[N : @tl.Pos, A] pos_guarded(v : @tl.Vec[N, A]) -> Int32 {
  // the bound is what makes the certificate available at all
  let _c = (@tl.Pos::pos_cert(()) : @tl.NatV[N])
  v.data.length()
}

///|
test "compile-time structural predicates" {
  let v3 : @tl.Vec[@tl.N3, Int32] = @tl.vec_from([1, 2, 3])
  let v2 : @tl.Vec[@tl.N2, Int32] = @tl.vec_from([1, 2])
  let v1 : @tl.Vec[@tl.N1, Int32] = @tl.vec_from([1])
  assert_eq(nat_guarded(v3), 3)
  assert_eq(even_guarded(v2), 2)
  assert_eq(odd_guarded(v3), 3)
  assert_eq(pos_guarded(v1), 1)
  // the same predicates, read back as compile-time constants
  assert_true(@tl.unwrap_flag((@tl.decide_even() : @tl.Flag[@tl.N4])))
  assert_true(@tl.unwrap_flag((@tl.decide_odd() : @tl.Flag[@tl.N3])))
}

///|
/// Certified type-level functions are *evaluated*: the compiler produces the
/// value.  (make proof-zero-cost shows these fold to machine constants.)
test "type level arithmetic is evaluated at compile time" {
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.N3])), 3)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Plus[@tl.N3, @tl.N4]])), 7)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Mul[@tl.N3, @tl.N2]])), 6)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Twice[@tl.N3]])), 6)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Pred[@tl.N3]])), 2)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Pred[@tl.Z]])), 0)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Pow[@tl.N2, @tl.N3]])), 8)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Fact[@tl.N4]])), 24)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Binom[@tl.N4, @tl.N2]])), 6)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Gcd[@tl.N6, @tl.N3]])), 3)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Max[@tl.N2, @tl.N4]])), 4)
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Min[@tl.N2, @tl.N4]])), 2)
  // Fibonacci: 0,1,1,2,3,5,8,13
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Fib[@tl.N7]])), 13)
  // nested expression
  assert_eq(@tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Plus[@tl.Mul[@tl.N2, @tl.N3], @tl.Pow[@tl.N2, @tl.N1]]])), 8)
}

///|
/// Propositions are decided at compile time.
test "propositions are compile-time constants" {
  assert_true(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.Leq[@tl.N2, @tl.N3]])))
  assert_false(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.Leq[@tl.N3, @tl.N2]])))
  assert_true(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.EqN[@tl.Plus[@tl.N1, @tl.N1], @tl.N2]])))
  assert_false(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.EqN[@tl.N1, @tl.N2]])))
  assert_true(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.Divides[@tl.N2, @tl.N4]])))
  assert_false(@tl.unwrap_flag((@tl.decide() : @tl.Flag[@tl.Divides[@tl.N2, @tl.N3]])))
}

///|
/// 同構即相同: the index isomorphisms are the identity on data.
test "index isos are the identity on data" {
  let v : @tl.Vec[@tl.Plus[@tl.Plus[@tl.N0, @tl.N1], @tl.N2], Int32] = @tl.vec_from([2, 3, 4])
  let w : @tl.Vec[@tl.Plus[@tl.N1, @tl.N2], Int32] = @tl.plus_assoc(v) |> @tl.plus_z_left
  assert_eq(w.data, [2, 3, 4])
  let u : @tl.Vec[@tl.Plus[@tl.N2, @tl.N1], Int32] = @tl.plus_comm(w)
  assert_eq(u.data, [2, 3, 4])
  let back = @tl.plus_comm(u)
  assert_eq(back.data, [2, 3, 4])
  let g : @tl.Graded[@tl.Neg[@tl.Neg[@tl.N2]], Int32] = @tl.graded_from([7, 8])
  assert_eq(@tl.neg_neg(g).data, [7, 8])
  let m : @tl.Vec[@tl.Mul[@tl.N2, @tl.N1], Double] = @tl.vec_from([1.0, 2.0])
  assert_eq(@tl.mul_one_right(m).data, [1.0, 2.0])
}

///|
/// The coercions agree with the certified arithmetic (soundness of the
/// theorem-as-function: both sides reify to the same integer).
test "coercions agree with certified arithmetic" {
  let lhs = @tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Plus[@tl.Plus[@tl.N2, @tl.N1], @tl.N3]]))
  let rhs = @tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Plus[@tl.N2, @tl.Plus[@tl.N1, @tl.N3]]]))
  assert_eq(lhs, rhs)
  assert_eq(lhs, 6)
  let a = @tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.Plus[@tl.N0, @tl.N3]]))
  let b = @tl.unwrap_nat((@tl.reflect() : @tl.NatV[@tl.N3]))
  assert_eq(a, b)
}

///|
/// Zero-cost kernels.
test "vec ops" {
  let a : @tl.Vec[@tl.N3, Double] = @tl.vec_from([1.0, 2.0, 3.0])
  let b : @tl.Vec[@tl.N3, Double] = @tl.vec_from([4.0, 5.0, 6.0])
  assert_eq(@tl.dot(a, b), 32.0)
  assert_eq(@tl.vadd(a, b).data, [5.0, 7.0, 9.0])
}

///|
test "iso laws" {
  let id : @tl.Iso[Array[Int32], Array[Int32]] = @tl.iso_identity()
  assert_true((id.to)([1, 2]) == [1, 2])
  let f : @tl.Iso[Int32, Int32] = @tl.iso_of(fn(x) { x + 1 }, fn(y) { y - 1 })
  assert_true(@tl.iso_check(f, 3, -2))
}
