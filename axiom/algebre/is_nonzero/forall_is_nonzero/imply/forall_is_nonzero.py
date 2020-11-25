from axiom.utility import plausible
from sympy.core.relational import LessThan, Equal, Unequal
from sympy import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.integers import ceiling
from sympy.concrete.expr_with_limits import ForAll
from sympy.core.function import Function
from axiom import algebre
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(*given):
    is_nonzero, forall_is_nonzero = given
    fa = axiom.is_nonzero(is_nonzero)
    fn1, limits = axiom.forall_is_nonzero(forall_is_nonzero)    
    n, fn, baseset = axiom.limits_is_nonzero_baseset(limits)    
    assert fn._subs(n, n + 1) == fn1
    a = axiom.is_Interval(baseset, integer=True, end=oo)
    assert fn._subs(n, a) == fa
    
    return ForAll[n:a:oo](Unequal(fn, 0), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True)    
    a = Symbol.a(integer=True)
    f = Function.f(nargs=(), shape=())
    Eq << apply(Unequal(f(a), 0), ForAll[n:Unequal(f(n), 0):Interval(a, oo, integer=True)](Unequal(f(n + 1), 0)))   

#     Eq << ForAll[n:Equal(KroneckerDelta(f(n), 0), 0):Interval(a, oo, integer=True)](Equal(KroneckerDelta(f(n + 1), 0), 0), plausible=True)
    
#     Eq << Eq[-1].this.function.simplify()
    
#     Eq << Eq[-1].this.limits[0][1].simplify()

    Eq << Eq[1].subs(n, a).split()
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Eq[1].subs(n, a + 1).split()
    
    Eq <<= Eq[-2] & Eq[-4]
    
    Eq << Eq[1].subs(n, a + 2).split()
    
    Eq <<= Eq[-2] & Eq[-3]
    
#     k = Symbol.k(integer=True, nonnegative=True)
#     Eq << Eq[1].subs(n, a + k).split()

    Eq << ~Eq[2]
    
    Eq << Eq[-1].bisect({a}).split()
    
    Eq << Eq[-1].limits_subs(n, n + 1)
    
    Eq << Eq[1].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
