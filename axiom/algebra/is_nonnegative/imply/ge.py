from util import *


@apply
def apply(given):
    import axiom
    xy = axiom.is_nonnegative(given)
    x, y = xy.of(Basic - Basic)
    
    return GreaterEqual(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(LessEqual(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    run()
