from util import *

import axiom


@apply
def apply(given):
    A, C = given.of(Equal)
    if not A.is_symbol:
        A, C = C, A    
    x, condition, base_set = axiom.is_ConditionSet(C)
    assert base_set.is_UniversalSet
    return ForAll[x:A](condition)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    
    f = Function.f(integer=True)

    Eq << apply(Equal(conditionset(x, f(x) > 0), A))
    
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()

