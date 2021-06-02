from util import *


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return GreaterEqual(Ceiling(x / d) * d, x, evaluate=evaluate)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True, positive=True)
     
    Eq << apply(x, d)
    
    Eq << Eq[-1] / d

        
if __name__ == '__main__':
    run()

