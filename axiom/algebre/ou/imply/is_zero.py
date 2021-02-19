from sympy.core.relational import Equality
from axiom.utility import prove, apply

from sympy import Symbol

from sympy.core.function import Function
import axiom

from sympy.core.mul import Times
from sympy.matrices.expressions.matexpr import ZeroMatrix
from axiom import algebre


@apply
def apply(given):
    or_eqs = axiom.is_Or(given)
    
    args = []
    for eq in or_eqs:
        lhs, rhs = axiom.is_Equal(eq)
        args.append(lhs - rhs)
    mul = Times(*args)    
    zero = ZeroMatrix(*mul.shape)
        
    return Equality(mul, zero)            




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equality(p, f(x)) | Equality(p, g(x)) | Equality(p, h(x)))
    
    Eq << ~Eq[1]
    
    Eq << algebre.is_nonzero.imply.et.apply(Eq[-1])
    
    Eq <<= ~Eq[0]


if __name__ == '__main__':
    prove(__file__)

