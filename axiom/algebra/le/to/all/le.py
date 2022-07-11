from util import *


@apply(given=None)
def apply(le, var=None):
    lhs, rhs = le.of(LessEqual)
    assert lhs.shape
    if var is None:
        var = le.generate_var(integer=True)
    return Equivalent(le, All[var:lhs.shape[0]](lhs[var] <= rhs[var]))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x <= y)

    Eq << Eq[0].this.rhs.apply(algebra.all_le.to.le.lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
