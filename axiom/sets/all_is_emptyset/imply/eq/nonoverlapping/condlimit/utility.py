from util import *


@apply
def apply(given, n):
    (xi, xj), (j, (i, _j)) = given.of(All[Equal[Intersection, EmptySet], Tuple[Unequal]])
    if j != _j:
        i, _j = _j, i
    assert j == _j

    if not xi.has(i):
        xi = xj
        assert xj.has(i)

    assert xj._subs(j, i) == xi

    return Equal(abs(Cup[i:0:n](xi)), Sum[i:0:n](abs(xi)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Range(2, oo), given=False)
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finiteset=True)

    Eq << apply(All(Equal(x[i] & x[j], x[i].etype.emptySet), (j, Unequal(j, i))), n)

    Eq << algebra.all.imply.suffice.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.lt)

    j_ = Symbol.j(integer=True, nonnegative=True)
    Eq << Eq[-1].subs(j, j_)

    Eq << algebra.suffice.imply.all.apply(Eq[-1])

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.intlimit.utility.apply(Eq[-1], n)


if __name__ == '__main__':
    run()

