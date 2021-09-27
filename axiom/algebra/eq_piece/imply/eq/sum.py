from util import *


@apply
def apply(self, sgm):
    ((xi, lt), (xi_1, _true)), yi = self.of(Equal[Piecewise])
    i, t = lt.of(Less)
    assert xi._subs(i, i + 1) == xi_1
    
    fyi, (_i, *ab) = sgm.of(Sum)
    assert _i == i
    if ab:
        _0, n = ab        
    else:
        domain = fyi.domain_defined(i)
        _0, n = domain.of(Range)
    assert _0 == 0
    n += 1
    
    assert t >= 0 and t < n
    assert fyi._has(yi)
    
    fxi = fyi._subs(yi, xi)
    return Equal(sgm, Sum[i:n](fxi) - fxi._subs(i, t))


@prove
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x, y = Symbol(real=True, shape=(oo,))
    t = Symbol(domain=Range(0, n))
    f = Function(real=True)
    Eq << apply(Equal(y[i], Piecewise((x[i], i < t),(x[i + 1], True))), Sum[i:n - 1](f(y[i])))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()