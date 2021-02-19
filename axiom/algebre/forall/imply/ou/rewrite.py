from sympy import *
from axiom.utility import prove, apply


def rewrite_as_Or(given):
    assert given.is_ForAll
    limits_dict = given.limits_dict
    eqs = []
    for var, domain in limits_dict.items():
        if isinstance(domain, list):
            cond = conditionset.conditionset(var, *domain).simplify()
        elif domain.is_set:
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

    
@apply
def apply(given):
    return rewrite_as_Or(given)


@prove
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

