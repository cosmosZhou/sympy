from util import *


@apply
def apply(given, index, wrt=None):
    [*eqs], *limits = given.of(All[Or])

    cond = eqs.pop(index)
    if wrt is None:
        wrt = cond.wrt
    else:
        cond._has(wrt)

    cond = cond.invert()

    domain = cond.domain_conditioned(wrt)
    for i, (x, *ab) in enumerate(limits):
        if x == wrt:
            if len(ab) == 2:
                a, b = ab
                assert not b.is_set
                domain = (Range if x.is_integer else Interval)(a, b)
                domain &= cond.domain_conditioned(wrt)
                limits[i] = (x, domain)
                return All(Or(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x, a, b, c = Symbol(real=True)

    f = Function(shape=(), real=True)

    Eq << apply(All[x:a:b]((x <= c) | (f(x) >= 1)), index=1)

    Eq << algebra.all.given.ou.apply(Eq[1])

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_intersect.given.ou, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.given.le.real, simplify=None)

    Eq << algebra.all.imply.ou.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-02-07
