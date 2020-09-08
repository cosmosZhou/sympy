from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Contains, Subset
from sympy import var
# given: A in B 
# => {A} subset B
@plausible
def apply(given):
    assert given.is_Contains
    e, s = given.args
    
    return Subset(e.set, s, given=given)


from sympy.utility import check


@check
def prove(Eq):
    e = var(integer=True).e
    s = var(dtype=dtype.integer).s
    contains = Contains(e, s, evaluate=False)
    
    Eq << apply(contains)
    
    Eq << Eq[-1].definition


if __name__ == '__main__':
    prove(__file__)

