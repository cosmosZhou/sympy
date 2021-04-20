from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


@apply(given=None)
def apply(given, index=None):
    x, intersection = axiom.is_Contains(given)
    
    ss = axiom.is_Intersection(intersection)
    if index is None:        
        et = [Contains(x, s) for s in ss]
    else:
        ss = ss[index]
        if isinstance(index, slice):
            et = [Contains(x, s) for s in ss]
            et.append(given)
        else:
            et = [Contains(x, ss), given]
    return Equivalent(given, And(*et))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Contains(x, A & B), index=0)
    
    Eq << algebra.equivalent.given.sufficient.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection)

    
if __name__ == '__main__':
    prove()

