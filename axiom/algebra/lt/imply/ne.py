from util import *
import axiom


@apply
def apply(given):
    return Unequal(*given.of(Less))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x < y)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])
    

if __name__ == '__main__':
    run()
