from util import *
import axiom


@apply
def apply(*given):    
    eq, f_eq = given
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = f_eq.of(Equal)
    return Equal(lhs - _lhs, rhs - _rhs)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Equal(a, b), Equal(x, y))
    
    Eq << Eq[0] - Eq[1]
        
    
if __name__ == '__main__':
    run()
