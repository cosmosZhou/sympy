from sympy.core.relational import Equal
from axiom.utility import prove, apply

from sympy import Symbol

from sympy.core.function import Function
import axiom

from sympy.core.mul import Mul
from sympy.matrices.expressions.matexpr import ZeroMatrix
from axiom import algebra


@apply
def apply(given):
    or_eqs = axiom.is_Or(given)
    
    args = []
    for eq in or_eqs:
        lhs, rhs = axiom.is_Equal(eq)
        args.append(lhs - rhs)
    mul = Mul(*args)    
    zero = ZeroMatrix(*mul.shape)
        
    return Equal(mul, zero)            




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)
    
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equal(p, f(x)) | Equal(p, g(x)) | Equal(p, h(x)))
    
    Eq << ~Eq[1]
    
    Eq << algebra.is_nonzero.imply.et.apply(Eq[-1])
    
    Eq <<= ~Eq[0]


if __name__ == '__main__':
    prove()

