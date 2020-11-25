from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, Subset
from sympy import Symbol


# given: A in B 
# => {A} subset B
@plausible
def apply(*given):
    contains, subset = given
    if contains.is_Subset:
        subset, contains = given
    assert contains.is_Contains and subset.is_Subset
    x, A = contains.args
    _A, B = subset.args
    assert A == _A
    return Contains(x, B, given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    Eq << apply(Contains(x, A), Subset(A, B))
    
#     Eq <<= Eq[0] & Eq[1]
    Eq <<= Eq[1] & Eq[0]
    

if __name__ == '__main__':
    prove(__file__)

