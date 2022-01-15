from util import *


@apply
def apply(self):
    x = self.of(Min[0])

    return Equal(self, -relu(-x))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(Min(0, x))

    Eq << Eq[0].this.lhs.apply(algebra.min.to.mul.max, factor=-1)

    Eq << Eq[-1].this.rhs.defun()





if __name__ == '__main__':
    run()
# created on 2021-12-25
