from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebra, sets
from sympy.core.power import sqrt


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equal(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], sqrt)


if __name__ == '__main__':
    prove()

