from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol, ForAll, And, Or, log
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)        
    return Or(Equal(log(lhs), log(rhs)), Equal(lhs, 0))


@prove
def prove(Eq):
    b = Symbol.b(real=True)
    a = Symbol.a(real=True)
    x = Symbol.x(domain=Interval(a, b))
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Equal(f(x), g(x)))
    
    Eq << Eq[1].subs(Eq[0])
    
    Eq << Eq[-1].astype(And)
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    #the following codes will issue an error because of illegal domain definition 
#     Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], log)


if __name__ == '__main__':
    prove(__file__)

