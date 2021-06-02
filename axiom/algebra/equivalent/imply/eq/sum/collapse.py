from util import *
import axiom



@apply
def apply(given, function):
    et_j, et_i = given.of(Equivalent)
    Aj_contains_j, Ai_contains_i = et_j.of(And)
    j, Aj = Aj_contains_j.of(Contains)
    i, Ai = Ai_contains_i.of(Contains)

    Bi_eq_i, Bj_contains_j = et_i.of(And)
    if not Bi_eq_i.is_Equal:
        Bi_eq_i, Bj_contains_j = Bj_contains_j, Bi_eq_i

    _i, Bi = Bi_eq_i.of(Equal)
    _j, Bj = Bj_contains_j.of(Contains)

    if i != _i:
        _i, Bi, _j, Bj = _j, Bj, _i, Bi

    assert _i == i
    assert _j == j

    assert not Aj._has(i)
    assert not Bi._has(j)
    return Equal(Sum[i:Ai, j:Aj](function), Sum[i:Bi](function._subs(j, Bj)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    f = Function.f(etype=dtype.integer)
    g = Function.g()
    h = Function.h(complex=True)

    Eq << apply(Equivalent(Contains(i, A) & Contains(j, f(i)), Contains(j, B) & Equal(i, g(j))), h(i, j))

    Eq << Eq[0].this.find(Equal).apply(sets.eq.to.contains)

    Eq << algebra.equivalent.imply.eq.sum.apply(Eq[-1], h(i, j))

    Eq << Eq[-1].this.rhs. apply(algebra.sum.simplify.conditionset)


if __name__ == '__main__':
    run()

