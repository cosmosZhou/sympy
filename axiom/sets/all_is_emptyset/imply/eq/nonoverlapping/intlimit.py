from util import *


# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@apply
def apply(given):
    assert given.is_ForAll
    eq = given.function
    assert eq.is_Equal
    limits = given.limits
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

    intersection, emptyset = eq.args
    assert emptyset.is_EmptySet
    xi, xj = intersection.args

    if not xi._has(i):
        xi, xj = xj, xi

    assert xi._subs(i, j) == xj
    return Equal(abs(Cup(xi, i_limit).simplify()), summation(abs(xi), i_limit))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)

    j_domain = Range(0, n) // {i}
    emptySet = x[i].etype.emptySet
    Eq << apply(ForAll[j: j_domain, i: n](Equal(x[i] & x[j], emptySet)))

    y = Symbol.y(Lamda[i](Piecewise((x[i], i < n), (emptySet, True))))

    Eq.y_definition = y.equality_defined()

    Eq << Eq.y_definition.apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq.yi_definition = Eq[-1].this().function.rhs.simplify()

    Eq << Eq.yi_definition.reversed

    Eq << algebra.all.all.imply.all_et.limits_intersect.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)

    Eq << algebra.all.all.imply.all_et.limits_intersect.apply(Eq[-1], Eq[-3].limits_subs(i, j), simplify=None)

    Eq.nonoverlapping = Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.subs)

    Eq << Eq.y_definition.apply(algebra.cond.imply.all.restrict, (i, n, oo))

    Eq << Eq[-1].this().function.rhs.simplify()

    Eq << Eq[-1].this.function.apply(sets.eq.imply.eq.intersection, y[j])

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (j, j_domain))

    Eq <<= Eq[-1] & Eq.nonoverlapping

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.util.setlimit.apply(Eq[-1])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.yi_definition, Eq[-1])


if __name__ == '__main__':
    run()

