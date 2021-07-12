from util import *


@apply
def apply(self):
    f, (m, domain) = self.of(Sum)
    n, expr, base_set = domain.image_set()
    
    assert expr.as_poly(n).degree() == 1    
    f = f._subs(m, expr)    

    return Equal(self, self.func(f, (n, base_set)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(integer=True)
    f = Symbol.f(shape=(oo,), real=True)
    h = Function.h(real=True)
    t = Function.t(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    Eq << apply(Sum[n:imageset(n, a * n + b, h(n) > 0)](f[n]))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    m = Symbol.m(integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(n, m)

    Eq << Eq[-1].this.lhs.limits_subs(m, m + b)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.sub, b)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.absorb)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.imageset.proportional)
    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.absorb)


if __name__ == '__main__':
    run()
from . import proportional
