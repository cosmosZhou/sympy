from util import *


@apply
def apply(self, offset):
    fx, (x, *ab) = self.of(Sum)    
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
    
    return Equal(self, Sum(fx, limit), evaluate=False)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    m = Symbol.m(integer=True)
    f = Function.f(integer=True)
    Eq << apply(Sum[n:1:m + 1](f(n)), 1)

    Eq << Eq[0] - Eq[0].lhs

    

    


if __name__ == '__main__':
    run()