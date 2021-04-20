from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebra

@apply
def apply(imply):
    e, AB = axiom.is_Contains(imply)
         
    return tuple(Contains(e, s) for s in axiom.is_Intersection(AB))

@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Contains(x, A & B))
    
    Eq << sets.contains.contains.imply.contains.intersect.apply(Eq[1], Eq[2])
    
if __name__ == '__main__':
    prove()

