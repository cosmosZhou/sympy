from util import *


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@apply
def apply(self, swap=False):
    x, y = self.of(Min)

    if swap:
        x, y = y, x

    return Equal(self, y - relu(-x + y))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[0].this.rhs.args[1].args[1].defun()

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul.to.min)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.min)


if __name__ == '__main__':
    run()
# created on 2020-12-29
# updated on 2020-12-29
