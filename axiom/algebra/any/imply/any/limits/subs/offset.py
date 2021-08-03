from util import *


@apply
def apply(given, offset):
    fx, (x, *ab) = given.of(Any)    
    fx = fx._subs(x, x + offset)
    if len(ab) == 2:
        a, b = ab
        a -= offset
        b -= offset
        limit = (x, a, b)
    elif ab:
        [domain] = ab
        if domain.is_boolean:
            domain = domain._subs(x, x + offset)            
        limit = (x, domain)
    else:
        limit = (x,)
    
    return Any(fx, limit)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True, given=True)
    f = Function.f(integer=True)
    Eq << apply(Any[n:1:m + 1](f(n) > 0), 1)

    Eq << ~Eq[1]

    Eq << algebra.all.imply.all.limits.subs.offset.apply(Eq[-1], -1)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()