from util import *
import axiom


@apply
def apply(given): 
    lhs, rhs = given.of(Equal)
    if lhs.is_nonzero:
        x = rhs
    if rhs.is_nonzero:
        x = lhs
        
    return Unequal(x, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, zero=False)
    Eq << apply(Equal(a, b))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    run()
