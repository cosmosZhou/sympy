from util import *

import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(function, *limits): 
    return ForAll(LessEqual(MIN(function, *limits), function), *limits)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
     
    Eq << apply(f(x), (x, 0, oo))
    
    Eq << Eq[0].simplify()
    
    
if __name__ == '__main__':
    run()

