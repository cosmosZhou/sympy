from util import *



def rewrite_as_Or(given):
    function, *limits = given.of(All)
    limits_dict = given.limits_dict
    eqs = []
    for var, domain in limits_dict.items():
        if isinstance(domain, list):
            cond = Element(var, conditionset(var, *domain).simplify()).simplify()
        elif domain.is_set:
            cond = Element(var, domain).simplify()
        else:
            assert domain.is_bool
            cond = domain
        eqs.append(cond.invert().simplify())

    if function.is_Or:
        eqs += function.args
    else:
        eqs.append(function)

    return Or(*eqs)


@apply
def apply(given):
    return rewrite_as_Or(given)


@prove
def prove(Eq):
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()

from . import limits_delete
from . import subs
# created on 2018-03-04
