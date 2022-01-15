from util import *


from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous


def of_continuous(cond):
    (limit, fxi), (xi, a, b) = cond.of(All[Equal])
    fz, (z, _xi, dirt) = limit.of(Limit)
    assert xi == _xi
    assert fz._subs(z, xi) == fxi
    assert dirt == 0
    return fz, (z, a, b)


def of_differentiable(cond, open=True, extended=False):
    if open:
        (derivative, R), (x, ab) = cond.of(All[Element])
        a, b = ab.of(Interval)
        assert ab.left_open and ab.right_open
    else:
        (derivative, R), (x, a, b) = cond.of(All[Element])

    if extended:
        assert R in ExtendedReals
    else:
        assert R in Reals

    fx, *limits_d = derivative.of(Derivative)
    assert len(limits_d) == 1
    _x, one = limits_d[0]
    assert _x == x
    assert one == 1

    return fx, (x, a, b)


def is_differentiable(f, a, b, x=None, open=True, plausible=None, extended=False):
    if x is None:
        x = Symbol.x(real=True)

    if open:
        left_open = right_open = True
    else:
        left_open = right_open = False

    kwargs = {}
    if plausible:
        kwargs['plausible'] = plausible

    if extended:
        S = Interval(-oo, oo, left_open=False, right_open=False)
    else:
        S = Reals
    return All[x:Interval(a, b, left_open=left_open, right_open=right_open)](Element(Derivative(f(x), x), S), **kwargs)


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
    a, b = Symbol(real=True)
    f = Function(shape=(), real=True)
    Eq << apply(a < b, is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))


if __name__ == '__main__':
    run()
# created on 2020-04-03
