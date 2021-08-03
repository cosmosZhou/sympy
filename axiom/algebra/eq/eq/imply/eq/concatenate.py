from util import *


@apply
def apply(eq_historic, eq_n):
    lhs, rhs = eq_historic.of(Equal)
    n = lhs.shape[0]

    if lhs.is_Lamda and rhs.is_Lamda and lhs.variable == rhs.variable:
        k = rhs.variable
    else:
        k = eq_historic.generate_var(integer=True)

    fx = lhs[k]
    gy = rhs[k]

    _lhs, _rhs = eq_n.of(Equal)

    assert fx._subs(k, n) == _lhs
    assert gy._subs(k, n) == _rhs
    return Equal(Lamda[k:n + 1](fx).simplify(), Lamda[k:n + 1](gy).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Equal(Lamda[k:n](f(k)), Lamda[k:n](g(k))), Equal(f(n), g(n)))

    Eq << algebra.eq.given.et.eq.blockmatrix.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
