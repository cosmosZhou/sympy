
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
from sympy.sets.conditionset import conditionset
from sympy.sets.contains import Contains
from axiom import sets


@plausible
def apply(given):
    assert given.is_Exists
    limits = [(x,) for x, *_ in given.limits]
    limits[0] = (limits[0][0], given.function)
    return Exists(given.limits_condition, *limits)


from axiom.utility import check


@check
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:g(e) > 0](f(e) > 0))
    
    A = Symbol.A(definition=conditionset(e, g(e) > 0))
    B = Symbol.B(definition=conditionset(e, f(e) > 0))
    
    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition
    
    Eq << Exists[e:A](Contains(e, B), plausible=True)
    
    Eq << Eq[-1].subs(Eq.B_definition)
    
    Eq << Eq[-1].subs(Eq.A_definition)
    
    Eq << sets.exists_contains.imply.exists_contains.limits_swap.apply(Eq[2], simplify=False)
    
    Eq << Eq[-1].subs(Eq.A_definition)
    
    Eq << Eq[-1].subs(Eq.B_definition)


if __name__ == '__main__':
    prove(__file__)

