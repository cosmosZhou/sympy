from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.concrete.limits import limits_dict
from axiom import algebre, sets


@apply(imply=True)
def apply(given):
    function, *limits = axiom.is_ForAll(given)
    axiom.is_Equal(function)
    
    dic = limits_dict(limits)
    assert len(dic) == 1
    (x, domain), *_ = dic.items()
    assert domain.is_integer and domain.is_Interval

    lhs, rhs = function.args
    return Equality(LAMBDA[x:domain](lhs).simplify(), LAMBDA[x:domain](rhs).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    
    Eq << apply(ForAll[i:n](Equality(f(i), g(i))))
    
    i_ = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0].subs(i, i_)
    
    Eq << Eq[1].this.lhs.limits_subs(i, i_)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, i_)
    

if __name__ == '__main__':
    prove(__file__)

