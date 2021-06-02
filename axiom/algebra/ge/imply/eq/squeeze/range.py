from util import *


@apply
def apply(given):
    x, b = given.of(GreaterEqual)
    domain = x.domain     
    a, b = domain.of(Range)
    
    return Equal(x, b - 1)


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True, given=True)
    x = Symbol.x(domain=Range(a, b + 1), given=True)
    
    Eq << apply(x >= b)
    
    Eq << ~Eq[-1] 
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    run()

