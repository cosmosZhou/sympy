from axiom.utility import prove, apply
from sympy import *


# given: A in B 
# => {A} subset B
@apply(imply=True)
def apply(given):
    assert given.is_Contains
    e, s = given.args
    
    return Subset(e.set, s)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s, evaluate=False)
    
    Eq << apply(contains)
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

