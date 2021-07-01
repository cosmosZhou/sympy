from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol.x(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol.w(shape=(oo,), nonnegative=True)
    else:
        assert w >= 0

    if i is None:
        i = Symbol.i(integer=True)

    if n is None:
        n = Symbol.n(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Suffice(Equal(Sum[i:n](w[i]), 1), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol.n(integer=True, positive=True, given=False)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol.w(shape=(oo,), nonnegative=True)
    f = Function.f(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq << calculus.is_positive.imply.suffice.Jesson.induct.apply(Eq[0], w=w, n=n)


if __name__ == '__main__':
    run()
from . import induct
