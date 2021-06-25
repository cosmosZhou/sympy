from util import *


@apply
def apply(is_positive, eq, x=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)    
    assert d == 2
    
    wi, (i, n) = eq.of(Equal[Sum[Tuple[0, Expr]], 1])
    assert wi >= 0
    domain = x_.domain    
    assert not domain.left_open and not domain.right_open
    if x is None:
        x = Symbol.x(shape=(oo,), domain=domain)
    assert x.domain_assumed == domain
    return GreaterEqual(Sum[i:n](wi * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](wi * x[i])))


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(domain=Interval(a, b))
    w = Symbol.w(shape=(oo,), nonnegative=True)
    f = Function.f(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, Equal(Sum[i:n](w[i]), 1))


if __name__ == '__main__':
    run()
