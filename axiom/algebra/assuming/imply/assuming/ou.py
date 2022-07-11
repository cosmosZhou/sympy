from util import *


@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Assuming)
    return Assuming(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from axiom import algebra
    
    p, q, r = Symbol(bool=True)
    Eq << apply(Assuming(p, q), cond=r)
    
    Eq << algebra.assuming.imply.ou.apply(Eq[0])
    
    Eq << algebra.assuming.given.ou.apply(Eq[1])
    
    Eq << algebra.ou.given.et.apply(Eq[-1])
    
    Eq << algebra.ou.given.ou.apply(Eq[-1], slice(0, 3, 2))


if __name__ == '__main__':
    run()
# created on 2022-01-27
