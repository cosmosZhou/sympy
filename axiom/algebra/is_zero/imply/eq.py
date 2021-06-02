from util import *


@apply
def apply(given, reverse=False):
    xy = given.of(Equal[0])
    x, y = xy.of(Basic - Basic)
    if reverse:
        x, y = y, x
    
    return Equal(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(Equal(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    run()
