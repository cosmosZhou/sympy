from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, log
from sympy.core.function import Function
import axiom
from axiom import algebra


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
    assert lhs.is_nonzero
    assert rhs.is_nonzero
        
    return Equal(log(lhs), log(rhs))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True, positive=True)
    g = Function.g(shape=(), real=True, positive=True)
    
    Eq << apply(Equal(f(x), g(x)))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    prove()


