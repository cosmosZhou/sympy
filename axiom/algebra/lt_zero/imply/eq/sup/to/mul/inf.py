from util import *


@apply
def apply(is_negative, self):
    a = is_negative.of(Expr < 0)
    fx, *limits = self.of(Sup)
    return Equal(self, a * Inf(fx / a, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a < 0, Sup[x:m:M](f(x) * a))

    Eq << algebra.lt_zero.imply.lt_zero.div.apply(Eq[0])

    Eq << algebra.lt_zero.imply.eq.inf.to.mul.sup.apply(Eq[-1], Eq[1].rhs.args[1]).reversed * a


if __name__ == '__main__':
    run()
# created on 2019-12-22
