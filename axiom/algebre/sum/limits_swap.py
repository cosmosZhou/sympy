from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)
    assert len(limits) == 2
    i_limit, j_limit = self.limits
    j, *_ = j_limit
    assert i_limit._has(j)
    
    (i, _a, _b), (j, a, b) = axiom.limits_are_Interval(limits)
    
    diff = j - _a
    if b.is_Infinity and _b.is_Infinity:
        ...    
    elif diff != b - _b or diff.has(i, j):
        return
        
#         j - diff <= i < _b
#         j <= i + diff < _b + diff = b
#         a <= j < b
# then: 
# a <= j <= i + diff < _b + diff = b 
# a <= j <= i + diff
# a <= i + diff < b  
# a - diff <= i < b - diff

    return Equality(self, self.func(function, (j, a, i + diff + 1), (i, a - diff, _b)))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    
    d = Symbol.d(integer=True)
    a = Symbol.a(integer=True)
    Eq << apply(Sum[i:j + d:n, j:a:n - d](f[i] * g[i, j]))

    Eq << Eq[0].this.lhs.apply(algebre.sum.bool)   
    
    Eq << Eq[-1].this.lhs.function.args[-1].arg.apply(sets.et.astype.et, split=False)
    
    Eq << Eq[-1].this.rhs.apply(algebre.sum.bool)
    
    Eq << Eq[-1].this.rhs.limits_swap()


if __name__ == '__main__':
    prove(__file__)

