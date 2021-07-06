from util import *


@apply(simplify=False)
def apply(given):
    (x, y), *limits = given.of(Any[Equal])
    cond = given.limits_cond
    return cond._subs(x, y)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Any[x:S](Equal(x, y)))
    
    Eq << Eq[0].simplify()

    
if __name__ == '__main__':
    run()
