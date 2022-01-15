from util import *


@apply
def apply(given, wrt=None):
    expr, *limits = given.of(All)

    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)

    limit = limits[i]

    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
    else:
        x, S = Tuple.as_setlimit(limit)

    domain = expr.domain_defined(x)    
    limit = (x, domain & S)
    limits[i] = limit
    return All(expr, *limits)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, n = Symbol(integer=True, positive=True, given=True)
    f = Symbol(real=True, shape=(n,), given=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:Range(m)](f[i] > 0))

    Eq << algebra.all.imply.ou.apply(Eq[1])

    Eq << ~Eq[0]

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-2], Eq[-1])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Range).apply(sets.range_min.to.union, simplify=None)

    Eq << Eq[-1].this(i).find(Element).simplify()


if __name__ == '__main__':
    run()
# created on 2022-01-08
