from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy.sets.contains import NotContains
from sympy import var
from sympy.concrete.expr_with_limits import Exists

# given e not in S
@plausible
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equality(e.set & s, S.EmptySet, given=given)


from sympy.utility import check


@check
def prove(Eq):
    s = var(dtype=dtype.integer).s
    e = var(integer=True).e

    Eq << apply(NotContains(e, s))

    Eq << Eq[-1].lhs.assertion()

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()[1]

    Eq << Eq[-1].this.function.simplify()
    
    Eq << Eq[-1].subs(Eq[-1].limits[0][0], e)
    
    Eq.plausible = Exists(Eq[-3].function & Eq[-1].function, *Eq[-1].limits, plausible=True)
    
    Eq << Eq.plausible.subs(Eq.plausible.function.args[0])
    
    Eq << Eq[-1].split()
    
    Eq << (Eq[-1] & Eq[0])
    
    Eq << Eq.plausible.split()
    
#     Eq << Eq[2].split()

if __name__ == '__main__':
    prove(__file__)

