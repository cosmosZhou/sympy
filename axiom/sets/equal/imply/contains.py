from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.concrete.summations import Sum
from sympy.functions.elementary.complexes import Abs
from axiom import sets


# given: |S| = 1
# Sum[x:S](x) in S
@apply(imply=True)
def apply(given, var=None):
    assert given.is_Equality
    S_abs, one = given.args
    assert S_abs.is_Abs and one == 1
    S = S_abs.arg
    assert S.is_set
    if var is None:
        var = S.element_symbol()
        assert not var.is_set
    return Contains(Sum[var:S](var), S)




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    S = Symbol.A(etype=dtype.integer * n)

    Eq << apply(Equality(Abs(S), 1))    
    
    Eq << sets.equal.imply.exists_equal.one.apply(Eq[0]).reversed
    
    Eq << Eq[1].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

