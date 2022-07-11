from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(MatProduct)
    assert i.is_integer
    front = function._subs(i, a)
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, MatMul(front, MatProduct[i:a + 1:b](function)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(MatProduct[i:0:n + 1](f(i)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=n > 0)

    Eq << Eq[2].this.lhs.apply(algebra.le_zero.imply.is_zero)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << algebra.infer.given.all.apply(Eq[1])

    n_ = Symbol('n', integer=True, positive=True)
    Eq << algebra.all.given.cond.subs.apply(Eq[-1], Eq[-1].variable, n_)

    Eq << Eq[-1].this.lhs.apply(discrete.matProd.to.matmul.pop_back)
    Eq << Eq[-1].this.rhs.args[1].apply(discrete.matProd.to.matmul.pop_back)


if __name__ == '__main__':
    run()
# created on 2020-11-16
