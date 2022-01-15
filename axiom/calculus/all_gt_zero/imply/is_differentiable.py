from util import *


@apply
def apply(all_is_positive):
    (fx, (x, d)), (x_, domain) = all_is_positive.of(All[Derivative > 0])
    assert x == x_
    assert d == 2
    assert domain.left_open and domain.right_open
    a, b = domain.of(Interval)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    f = lambda x: fx._subs(x_, x)
    return is_differentiable(f, a, b)


@prove(proved=False)
def prove(Eq):
    a, b, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True, right_open=True)](Derivative(f(x), (x, 2)) > 0))


if __name__ == '__main__':
    run()
# created on 2020-03-30
