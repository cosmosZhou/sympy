from util import *
from axiom.calculus.integral.intermediate_value_theorem import is_continuous
import axiom


def is_differentiable(f, a, b, x=None):
    if x is None: 
        x = Symbol.x(real=True)
        
    return ForAll[x:Interval(a, b, left_open=True, right_open=True)](Contains(Derivative(f(x), x), Reals))


@apply
def apply(*given):
    is_continuous, is_differentiable, equal = given
    fz, (z, a, b) = axiom.is_continuous(is_continuous)
    _fz, (_z, _a, _b) = axiom.is_differentiable(is_differentiable)
    assert _fz == fz
    assert _z == z
    assert _a == a
    assert _b == b
    assert a < b
    fa, fb = equal.of(Equal)
    assert fz._subs(z, a) == fa
    assert fz._subs(z, b) == fb
    
    return Exists[z:Interval(a, b, left_open=True, right_open=True)](Equal(Derivative(fz, z), 0))               


@prove(surmountable=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True))
    f = Function.f(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))


if __name__ == '__main__':
    run()

