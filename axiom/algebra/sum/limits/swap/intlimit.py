from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


def limits_swap(self):
    function, *limits = self.args
    assert len(limits) == 2
    i_limit, j_limit = self.limits
    j, *_ = j_limit
    assert i_limit._has(j)
    
    limit_i, limit_j = axiom.limits_are_Interval(limits)
    if len(limit_i) == 3:
        i, _a, _b = limit_i
    else:
        assert len(limit_i) == 1
        i = limit_i[0]
        _ab = function.domain_defined(i)
        _a, _b = axiom.is_Interval(_ab)
        
    if len(limit_j) == 3:
        j, a, b = limit_j
    else:
        assert len(limit_j) == 1
        j = limit_j[0]
        ab = function.domain_defined(j)
        a, b = axiom.is_Interval(ab)
    
    diff = j - _a
    if b.is_Infinity and _b.is_Infinity:
        ...    
    elif diff != b - _b or diff.has(i, j):
# _a <= i < _b
# _a <= i < j - diff
# _a + diff <= i + diff < j
# a <= i + diff < j
# a <= j < b
# then
# a <= i + diff < j < b 
# a - diff <= i < j - diff

        diff = j - _b + 1
        
        diff_a = a - _a
        if diff == diff_a:
            return self.func(function, (j, i + diff, b), (i, _a, b - diff))
        elif diff == diff_a + 1:
            return self.func(function, (j, i + diff, b), (i, _a, b - diff + 1))
        else:
            raise            
    
# _a <= i < _b
# j - diff <= i < _b
# j <= i + diff < _b + diff = b
# a <= j < b
# then: 
# a <= j <= i + diff < _b + diff = b 
# a <= j <= i + diff
# a <= i + diff < b  
# a - diff <= i < b - diff

    return self.func(function, (j, a, i + diff + 1), (i, a - diff, _b))

    
@apply
def apply(self):
    assert self.is_Sum    
    return Equal(self, limits_swap(self))


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

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)   
    
    Eq << Eq[-1].this.lhs.function.args[-1].arg.apply(sets.et.transform.i_ge_j)
    
    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)
    
    Eq << Eq[-1].this.rhs.limits_swap()


if __name__ == '__main__':
    prove()

