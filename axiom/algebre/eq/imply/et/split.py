from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
        
    assert lhs.is_DenseMatrix and rhs.is_DenseMatrix
 
    args = [Equal(lhs, rhs).simplify() for lhs, rhs in zip(lhs._mat, rhs._mat)]
    return And(*args)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    Eq << apply(Equality(Matrix([a, b]), Matrix([c, d])))    
    
    Eq << algebre.et.given.cond.apply(Eq[1])
    
    Eq << Eq[0] @ Matrix([0, 1])
    
    Eq << Eq[0] @ Matrix([1, 0])
    

if __name__ == '__main__':
    prove(__file__)

