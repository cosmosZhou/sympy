from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


def merge(given):
    function, *limits = axiom.is_ForAll(given)
    
    limit_slice, limit_index = limits
    
    if not limit_slice[0].is_Slice:
        limit_index, limit_slice = limits
        
    x_slice, space = limit_slice
    _domain, n = axiom.is_CartesianSpace(space)
    
    x, slices = axiom.is_Slice(x_slice)
    
    if len(limit_index) == 3:
        x_index, a, b = limit_index
        integer = x_index.is_integer
        domain = Interval(a, b, right_open=integer, integer=integer)
        _x, index = x_index.args
    else: 
        x_index, domain = limit_index
        if x_index.is_Slice:
            domain, size = axiom.is_CartesianSpace(domain)
            assert size == x_index.shape[0]
            _x, index = x_index.args
        else:
            _x, index = axiom.is_Indexed(x_index)
        
    assert _domain == domain
    
    assert _x == x

    start, stop = slices    
    if index == stop: 
        stop += 1
    elif index == start - 1:
        start = index
    else:
        assert index.is_Tuple
        _start, _stop = index
        assert _stop == start
        start = _start
        
    return ForAll[x[start:stop]:CartesianSpace(domain, stop - start)](function)

    
@apply
def apply(given):
    return merge(given)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))
    
    Eq << algebra.forall.given.sufficient.apply(Eq[1])
    
    Eq << Eq[-1].this.lhs.apply(algebra.forall.imply.et.split, cond={n})
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[0])
    
    Eq << Eq[-1].this.lhs.args[0].simplify()
    

if __name__ == '__main__':
    prove()

