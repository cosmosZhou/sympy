from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    front = function._subs(i, a - 1)
    return Equal(self, Piecewise((Sum[i:a - 1:b](function) - front, b >= a), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:1:n](f(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.split, cond={0})

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=n >= 1)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << Eq[-1].this.lhs.apply(algebra.lt.imply.sum_is_zero, Eq[-1].find(Sum))

    Eq << Eq[-2].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.find(Less).reversed

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.imply.gt.relax, lower=0)

    Eq << algebra.infer.given.infer.subs.bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-03-25
