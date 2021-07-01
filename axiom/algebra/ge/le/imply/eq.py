from util import *


@apply
def apply(greater_than, less_than):
    a, b = greater_than.of(GreaterEqual)
    _a, _b = less_than.of(LessEqual)
    assert a == _a
    assert b == _b

    return Equal(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(a >= b, a <= b)
    
    Eq <<= Eq[0] & Eq[1]
    
    


if __name__ == '__main__':
    run()