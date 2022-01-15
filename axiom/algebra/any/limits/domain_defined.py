from util import *


@apply(given=None)
def apply(given, wrt=None):
    expr, *limits = given.of(Any)

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
    return Equivalent(given, Any(expr, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    
    m, n = Symbol(integer=True, positive=True)
    f = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Any[i:Range(m)](f[i] > 0))
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.domain_defined)
    Eq << Eq[-1].this.lhs.apply(algebra.any.given.any.limits.domain_defined)


if __name__ == '__main__':
    run()
# created on 2022-01-08
