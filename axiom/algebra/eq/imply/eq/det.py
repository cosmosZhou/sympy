from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebra, sets
from sympy.matrices.expressions.determinant import det


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equal(det(lhs), det(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    m = Symbol.m(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(m, m), integer=True)
    g = Function.g(shape=(m, m), integer=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], det)


if __name__ == '__main__':
    prove()

