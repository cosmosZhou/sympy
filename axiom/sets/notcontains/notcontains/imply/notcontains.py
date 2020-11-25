
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol


# given e not in S


# => S - {e} = S
@plausible
def apply(*given):
    notcontains1, notcontains2 = given
    assert notcontains1.is_NotContains    
    assert notcontains2.is_NotContains
    
    e, A = notcontains1.args
    _e, B = notcontains2.args
    assert e == _e
    
    return NotContains(e, A | B, given=given)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)    

    Eq << apply(NotContains(e, A), NotContains(e, B))
    
    Eq << Eq[-1].split()
    
if __name__ == '__main__':
    prove(__file__)

