from util import *


@apply
def apply(given):
    (xi, xj), *limits = given.of(All[Equal[Intersection, EmptySet]])

    if len(limits) == 2:
        (j, j_domain), i_limit = limits
        assert j_domain.is_Complement
        _, i = j_domain.args
        assert i.is_FiniteSet and len(i) == 1
        i, *_ = i.args
    else:
        assert len(limits) == 1
        i, j_domain = limits[0]
        assert j_domain.is_Complement

        universe, j = j_domain.args
        assert j.is_FiniteSet and len(j) == 1
        j, *_ = j.args

        i_limit = (i, universe)

    if not xi._has(i):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    return Equal(abs(Cup(xi, i_limit).simplify()), Sum(abs(xi), i_limit))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)

    j_domain = Range(0, n) - {i}
    emptySet = x[i].etype.emptySet
    Eq << apply(All[j: j_domain, i: n](Equal(x[i] & x[j], emptySet)))

    y = Symbol.y(Lamda[i](Piecewise((x[i], i < n), (emptySet, True))))

    Eq.y_definition = y[i].this.definition

    Eq << Eq.y_definition.apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq.yi_definition = Eq[-1].this().function.rhs.simplify()

    Eq << Eq.yi_definition.reversed

    Eq << algebra.all.all.imply.all_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)

    Eq << algebra.all.all.imply.all_et.apply(Eq[-1], Eq[-3].limits_subs(i, j), simplify=None)

    Eq.nonoverlapping = Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.subs)

    Eq << Eq.y_definition.apply(algebra.cond.imply.all.restrict, (i, n, oo))

    Eq << Eq[-1].this().function.rhs.simplify()

    Eq << Eq[-1].this.function.apply(sets.eq.imply.eq.intersection, y[j])

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (j, j_domain))

    Eq <<= Eq[-1] & Eq.nonoverlapping

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.setlimit.utility.apply(Eq[-1])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.yi_definition, Eq[-1])


if __name__ == '__main__':
    run()

del utility
from . import utility
