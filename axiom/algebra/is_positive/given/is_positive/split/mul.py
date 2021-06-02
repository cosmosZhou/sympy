from util import *
import axiom



@apply
def apply(given):
    mul = axiom.is_positive(given)
    args = mul.of(Mul)        
    return tuple(Greater(arg, 0) for arg in args)


@prove
def prove(Eq):
    x = Symbol.x(real=True)    
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
        
    Eq << apply(x * y * z > 0)

    Eq << Eq[1] * Eq[2] * Eq[3]
    
if __name__ == '__main__':
    run()

