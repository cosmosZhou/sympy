from util import *


@apply
def apply(is_positive, eq, x=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)    
    assert d == 2
    
    wi, (i, n) = eq.of(Equal[Sum[Tuple[0, Expr]], 1])
    assert wi >= 0
    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol.x(shape=(oo,), domain=domain)
    assert x.domain_assumed == domain
    return GreaterEqual(Sum[i:n](wi * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](wi * x[i])))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol.w(shape=(oo,), nonnegative=True)
    f = Function.f(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, Equal(Sum[i:n](w[i]), 1))

    Eq << calculus.is_positive.imply.suffice.Jesson.apply(Eq[0], w=w, n=n, x=Eq[-1].lhs.find(f).arg.base)
    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
