from util import *

import axiom


@apply(given=None)
def apply(given):
    x, fx = given.of(Equal)
    if not x.is_Symbol:
        x, fx = fx, x
        
    assert x.is_given is None
    return Equivalent(given, Contains(x, conditionset(x, given)), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f()

    Eq << apply(Equal(f(x), x))
    
    Eq << Eq[-1].this.rhs.rhs.simplify()
    
if __name__ == '__main__':
    run()

