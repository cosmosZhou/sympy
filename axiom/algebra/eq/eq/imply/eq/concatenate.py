from util import *


@apply
def apply(*given):
    import axiom
    eq_historic, eq_n = given
    lhs, rhs = eq_historic.of(Equal)
    _lhs, _rhs = eq_n.of(Equal)
    fx, *limits_x = lhs.of(Lamda)
    gy, *limits_y = rhs.of(Lamda)
    k, a, b = axiom.limit_is_Interval(limits_x)
    _k, _a, _b = axiom.limit_is_Interval(limits_y)
    assert k == _k
    assert a == _a
    assert b == _b
    assert a.is_zero
    n = b
    assert fx._subs(k, n) == _lhs
    assert gy._subs(k, n) == _rhs
    return Equal(Lamda[k:n + 1](fx), Lamda[k:n + 1](gy))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(Equal(Lamda[k:n](f(k)), Lamda[k:n](g(k))), Equal(f(n), g(n)))

    Eq << Eq[-1].apply(algebra.eq.given.et.split.blockmatrix, Slice[-1:])

    Eq << algebra.et.given.conds.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
