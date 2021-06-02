from util import *


@apply
def apply(given, index, wrt=None):
    [*eqs], *limits = given.of(ForAll[Or])

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
                return ForAll(Or(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)

    f = Function.f(shape=(), real=True)

    Eq << apply(ForAll[x:a:b]((x <= c) | (f(x) >= 1)), index=1)

    Eq << algebra.all.given.ou.apply(Eq[1])

    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.given.ou.split.intersection, simplify=None)

    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.given.le.real, simplify=None)

    Eq << algebra.all.imply.ou.apply(Eq[0])


if __name__ == '__main__':
    run()

