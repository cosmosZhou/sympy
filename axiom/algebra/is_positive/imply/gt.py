from util import *
import axiom



@apply
def apply(given):
    xy = axiom.is_positive(given)
    x, y = axiom.is_Subtract(xy)
    
    return Greater(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(Less(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed
    
    

if __name__ == '__main__':
    run()
