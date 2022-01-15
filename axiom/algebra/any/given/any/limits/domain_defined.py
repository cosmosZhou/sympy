from util import *


@apply
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
    return Any(expr, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True, given=True)
    f = Symbol(real=True, shape=(n,), given=True)
    i = Symbol(integer=True)
    Eq << apply(Any[i:Range(m)](f[i] > 0))

    Eq << ~Eq[0]

    Eq << algebra.all.imply.all.limits.domain_defined.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-01-08
