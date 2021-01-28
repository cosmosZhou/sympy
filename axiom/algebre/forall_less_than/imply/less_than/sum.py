from axiom.utility import prove, apply
from sympy.core.relational import Equality, LessThan
from sympy import Symbol, ForAll, Slice, Sum
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_less_than(given)
    lhs, rhs = eq.args
    
    return LessThan(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[i:n](LessThan(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << algebre.forall_greater_than.imply.greater_than.sum.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)

