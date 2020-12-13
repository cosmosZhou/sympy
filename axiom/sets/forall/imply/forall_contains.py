from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.sets.conditionset import conditionset

from sympy import Symbol
from sympy import ForAll

from sympy.core.function import Function
from sympy.core.symbol import dtype, Wild
from sympy.sets.contains import Contains


@plausible
def apply(given, P):
    assert given.is_ForAll
    assert P.is_ConditionSet or P.definition.is_ConditionSet
    _, y, cond = P.image_set()
    f_gx = given.function
    pattern = cond._subs(y, Wild(y.name, **y.assumptions0), symbol=False)
    
    res = f_gx.match(pattern)
    gx, *_ = res.values()

    return given.func(Contains(gx, P), *given.limits)


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(m,))
    A = Symbol.A(etype=dtype.complex * n)
    f = Function.f(nargs=(m,), shape=(), integer=True)
    g = Function.g(nargs=(n,), shape=(m,))
    
    P = Symbol.P(definition=conditionset(y, Equality(f(y), 1)))
    Eq << apply(ForAll[x:A](Equality(f(g(x)), 1)), P)
    
    Eq << Eq[-1].definition


if __name__ == '__main__':
    prove(__file__)
