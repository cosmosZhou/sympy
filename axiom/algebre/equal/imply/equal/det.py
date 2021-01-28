from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre, sets
from sympy.matrices.expressions.determinant import det


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equality(det(lhs), det(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    m = Symbol.m(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(m, m), integer=True)
    g = Function.g(nargs=(), shape=(m, m), integer=True)
    
    Eq << apply(Equality(f(i), g(i)))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], det)


if __name__ == '__main__':
    prove(__file__)

