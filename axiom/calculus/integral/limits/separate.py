from util import *


@apply
def apply(sgm):
    function, *limits = sgm.of(Integral)
    assert len(limits) > 1
    limit, *limits = limits

    function = sgm.func(function, limit).simplify()

    return Equal(sgm, sgm.func(function, *limits))


@prove
def prove(Eq):
    from axiom import calculus

    x, y, a, b, c, d = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b, y:c:d](f(y) * g(x, y)))

    Eq << Eq[-1].this.rhs.expr.apply(calculus.mul.to.integral)


if __name__ == '__main__':
    run()
# created on 2020-06-06
