from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, ArgMin
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(ArgMin(lhs, *limits).simplify(), ArgMin(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equality(f(i), g(i)), (i, 0, n))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], ArgMin[i:n], simplify=False)    

if __name__ == '__main__':
    prove(__file__)

