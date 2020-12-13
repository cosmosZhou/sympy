from axiom.utility import plausible
from sympy.core.relational import Unequal, Equality
from sympy import Symbol
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(given):
    assert given.is_Unequality
    assert given.rhs.is_zero
    assert given.lhs.is_KroneckerDelta
    return Equality(*given.lhs.args)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(KroneckerDelta(a, b), 0))
    
    Eq << Eq[0].simplify()


if __name__ == '__main__':
    prove(__file__)
