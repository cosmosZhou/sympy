from util import *


@apply
def apply(self, factor=None):
    args = self.of(Min)

    if factor is None:
        common_factors = None

        for arg in args:
            if not arg.is_Mul:
                return

            if common_factors is None:
                common_factors = {*arg.args}
            else:
                common_factors &= {*arg.args}

        if common_factors:
            factor = Mul(*common_factors)

    assert factor < 0
    args = [arg / factor for arg in args]
    return Equal(self, factor * Max(*args))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    r = Symbol(real=True, negative=True)
    Eq << apply(Min(x * r, y * r))

    Eq << Eq[0].this.lhs.apply(algebra.min.to.piece)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.max.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.to.mul)

    Eq << Eq[-1].this.find(LessEqual).reversed


if __name__ == '__main__':
    run()
# created on 2020-01-26
