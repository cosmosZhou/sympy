from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Integrate
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo
from sympy.core.function import Derivative


@apply(imply=True)
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    limits = [x for x, *_ in limits]
    
    return Equality(Derivative(lhs, *limits), Derivative(rhs, *limits))


@prove
def prove(Eq):    
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(x), g(x)), (x,))
    
    Eq << Eq[1].subs(Eq[0])
    
if __name__ == '__main__':
    prove(__file__)

