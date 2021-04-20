from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


def rewrite_as_Or(given):
    assert given.is_ForAll
    limits_dict = given.limits_dict
    eqs = []
    for var, domain in limits_dict.items():
        if isinstance(domain, list):
            cond = conditionset(var, *domain).simplify()
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
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer, given=True)
    
    Eq << apply(ForAll[x:A](f(x) > 0))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    prove()

from . import limits_delete
from . import subs
