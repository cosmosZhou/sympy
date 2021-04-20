from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, ForAll, Slice, MIN
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebra, sets
from sympy.core.symbol import dtype


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equal(MIN(lhs, *limits).simplify(), MIN(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], MIN[i:n], simplify=False)    

if __name__ == '__main__':
    prove()

