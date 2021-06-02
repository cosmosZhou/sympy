from util import *
import axiom



@apply
def apply(*given):
    is_positive_x, is_positive_y = given
    x = axiom.is_positive(is_positive_x)
    y = axiom.is_positive(is_positive_y)
    return Greater(x + y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x > 0, y > 0)
    
    Eq << Eq[0] + Eq[1]

    
if __name__ == '__main__':
    run()
