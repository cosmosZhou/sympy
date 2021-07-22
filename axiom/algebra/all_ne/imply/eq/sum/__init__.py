from util import *


@apply
def apply(given, sgm):
    (y, xi), (i, n) = given.of(All[Unequal, Tuple[0]])
    ft, (t, s) = sgm.of(Sum)
    xj, (j, _n) = s.of(Cup[FiniteSet, Tuple[0]])
    assert xj._subs(j, i) == xi
    assert n == _n
    
    return Equal(sgm, Sum[t:s | {y}](ft) - ft._subs(t, y), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(complex=True, shape=(oo,))
    y = Symbol.y(complex=True)
    t = Symbol.t(complex=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(complex=True)
    Eq << apply(All[i:n](Unequal(y, x[i])), Sum[t:x[:n].set_comprehension()](f(t)))

    Eq << sets.all_ne.imply.intersection_is_emptyset.apply(Eq[0])

    Eq << sets.intersection_is_emptyset.imply.eq.sum.apply(Eq[-1], Eq[1].rhs.args[1])

    Eq << Eq[-1].this.apply(algebra.eq.transposition, rhs=0)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
from . import double_limits
