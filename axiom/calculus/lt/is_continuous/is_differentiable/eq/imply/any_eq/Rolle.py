from util import *


from axiom.calculus.integral.intermediate_value_theorem import is_continuous


def of_continuous(cond):
    (limit, fxi), (xi, a, b) = cond.of(All[Equal])
    fz, (z, _xi, dirt) = limit.of(Limit)
    assert xi == _xi    
    assert fz._subs(z, xi) == fxi
    assert dirt == 0
    return fz, (z, a, b)    


def of_differentiable(cond, open=True):
    if open:
        (derivative, R), (x, ab) = cond.of(All[Contains])
        a, b = ab.of(Interval)    
        assert ab.left_open and ab.right_open
    else:
        (derivative, R), (x, a, b) = cond.of(All[Contains])
        
    assert R.is_UniversalSet
    
    fx, *limits_d = derivative.of(Derivative)
    assert len(limits_d) == 1
    _x, one = limits_d[0]
    assert _x == x
    assert one == 1
    
    return fx, (x, a, b)


def is_differentiable(f, a, b, x=None, open=True):
    if x is None: 
        x = Symbol.x(real=True)
        
    if open:
        left_open = right_open = True
    else:
        left_open = right_open = False
        
    return All[x:Interval(a, b, left_open=left_open, right_open=right_open)](Contains(Derivative(f(x), x), Reals))


@apply
def apply(lt, is_continuous, is_differentiable, equal):
    a, b = lt.of(Less)
    fz, (z, _a, _b) = of_continuous(is_continuous)
    _fz, (_z, __a, __b) = of_differentiable(is_differentiable)
    assert _fz == fz
    assert _z == z
    assert _a == a == __a
    assert _b == b == __b
    
    fa, fb = equal.of(Equal)
    assert fz._subs(z, a) == fa
    assert fz._subs(z, b) == fb
    
    return Any[z:Interval(a, b, left_open=True, right_open=True)](Equal(Derivative(fz, z), 0))               


@prove(proved=False)
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    Eq << apply(a < b, is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))


if __name__ == '__main__':
    run()