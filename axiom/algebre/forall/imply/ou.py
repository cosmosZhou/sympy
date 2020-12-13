from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol, ForAll, Or
from sympy.core.function import Function


@plausible
def apply(given):
    assert given.is_ForAll
    limits_dict = given.limits_dict
    eqs = []
    for var, domain in limits_dict.items():
        if domain.is_set:
            cond = Contains(var, domain).simplify()
        else:
            assert domain.is_boolean
            cond = domain
        eqs.append(cond.invert().simplify())

    if given.function.is_Or:
        eqs += given.function.args
    else:
        eqs.append(given.function)

    return Or(*eqs)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](f(x) > 0))
    y = Symbol.y(integer=True)
    Eq << Eq[0].subs(x, y)
    
    Eq << Eq[-1].subs(y, x)


if __name__ == '__main__':
    prove(__file__)

