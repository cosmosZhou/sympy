from util import *


@apply
def apply(given):
    x, b = given.of(LessEqual)
    domain = x.domain     
    b, a = domain.of(Range)
    
    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True, given=True)
    x = Symbol.x(domain=Range(b, a), given=True)
    
    Eq << apply(x <= b)
    
    Eq << ~Eq[-1] 
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()