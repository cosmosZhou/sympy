from util import *



@apply
def apply(self, evaluate=False):
    from axiom.algebra.mul.to.min import extract
    rhs = extract(Max, self)

    return Equal(self, rhs, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    t = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    Eq << apply(t * Max(x, y))
    Eq << Eq[0].this.rhs.apply(algebra.max.to.mul)


if __name__ == '__main__':
    run()
# created on 2020-01-29
# updated on 2020-01-29
