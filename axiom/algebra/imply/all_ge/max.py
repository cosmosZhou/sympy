from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(maximize):
    function, *limits = maximize.of(Maximize)
    return All(GreaterEqual(maximize, function), *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True)
    N = Symbol.N(integer=True)
    
    Eq << apply(Maximize[n:N + 1](abs(x[n])))
        
#     Eq << ~Eq[-1]
    
    _n = Symbol.n(domain=Range(0, N + 1))
    Eq << Eq[-1].limits_subs(n, _n)
    
    Eq << Eq[-1].this.lhs.limits_subs(n, _n)
    
#     Eq << Eq[-1].simplify()

    
if __name__ == '__main__':
    run()

