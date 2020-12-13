from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, Subset
from sympy import Symbol
# given: A in B 
# => {A} subset B
@plausible
def apply(given):
    assert given.is_Contains
    e, s = given.args
    
    return Subset(e.set, s)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s, evaluate=False)
    
    Eq << apply(contains)
    
    assert Eq[0].plausible is None
    Eq << Eq[-1].definition


if __name__ == '__main__':
    prove(__file__)

