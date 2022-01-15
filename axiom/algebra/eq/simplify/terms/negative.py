from util import *


def simplify_negative_terms(given):
    lhs, rhs = given.args

    lhs_positive = []
    rhs_positive = []

    if lhs.is_Add:
        lhs_args = lhs.args
    else:
        lhs_args = [lhs]

    for arg in lhs_args:
        if arg._coeff_isneg():
            rhs_positive.append(-arg)
        else:
            lhs_positive.append(arg)

    if rhs.is_Add:
        rhs_args = rhs.args
    else:
        rhs_args = [rhs]

    for arg in rhs_args:
        if arg._coeff_isneg():
            lhs_positive.append(-arg)
        else:
            rhs_positive.append(arg)

    return given.func(Add(*lhs_positive), Add(*rhs_positive))


@apply(given=None)
def apply(given):
    assert given.is_Equal
    return Equivalent(given, simplify_negative_terms(given))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, a, b = Symbol(real=True, shape=(n,))


    Eq << apply(Equal(x - a, y - b))

    Eq << Eq[-1].this.lhs + a

    Eq << Eq[-1].this.lhs + b


if __name__ == '__main__':
    run()
# created on 2021-07-28
