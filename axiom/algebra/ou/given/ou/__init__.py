from util import *


@apply
def apply(imply, index=None):
    eqs = imply.of(Or)
    assert isinstance(index, slice)
    
    return Or(*eqs[index])


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    f = Function.f(real=True, given=True)
    
    Eq << apply((f(y) > 0) | (f(x) > 0) | (f(b) > 0), index=Slice[0:2])
    
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]
    

if __name__ == '__main__':
    run()


del collect
from . import collect
