from util import *


@apply
def apply(given, offset):
    fx, (x, *ab) = given.of(All[Tuple])    
    fx = fx._subs(x, x + offset)
    if len(ab) == 2:
        a, b = ab
        a -= offset
        b -= offset
        limit = (x, a, b)
    else:
        [domain] = ab
        if domain.is_boolean:
            domain = domain._subs(x, x + offset)
            limit = (x, domain)
    
    return All(fx, limit)


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)
    Eq << apply(All[n:1:m + 1](f(n) > 0), 1)

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], n, n + 1)

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.notcontains.sub, 1)

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=n)


if __name__ == '__main__':
    run()