from util import *
import axiom



@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)
    
    limits = [x for x, *_ in limits]
    
    return Equal(Derivative(lhs, *limits), Derivative(rhs, *limits))


@prove
def prove(Eq): 
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(x), g(x)), (x,))
    
    Eq << Eq[1].subs(Eq[0])

    
if __name__ == '__main__':
    run()
