from util import *


@apply
def apply(self, strict=False):
    if strict:
        cond = self > 0
    else:
        cond = self >= 0
    return Equal(self, Piecewise((relu(self), cond), (-relu(-self), True)))


@prove
def prove(Eq):
    from axiom import algebra, keras

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.expr.to.piece.apply(x, lower=S.Zero)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(Max).apply(keras.max.to.relu)

    Eq << Eq[-1].this.find(Min).apply(keras.min.to.neg.relu)





if __name__ == '__main__':
    run()
# created on 2021-12-25
