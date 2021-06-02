from util import *


@apply
def apply(given):
    (xi, (i, zero, n)), _n = given.of(Equal[Abs[Cup[FiniteSet]]])
    assert zero == 0
    assert n == _n

    j = xi.generate_var(integer=True)
    xj = xi.subs(i, j)

    return ForAll[j:i, i:n](Unequal(xi, xj))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True, given=True)
    Eq << apply(Equal(abs(x[:n].set_comprehension()), n))

    xi, xj = Eq[1].function.args
    x, i = xi.args
    b = Symbol.b(Lamda[i:n](x[i].set))
    Eq << abs(Cup[i:n](b[i])).this.arg.function.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    Eq << Sum[i:n](abs(b[i])).this.function.arg.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << sets.eq.imply.all_is_emptyset.apply(Eq[-1])

    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()

from . import complement
