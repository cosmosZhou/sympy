from util import *


@apply(given=None)
def apply(ge, var=None):
    lhs, rhs = ge.of(GreaterEqual)
    assert lhs.shape
    if var is None:
        var = ge.generate_var(integer=True)
    return Equivalent(ge, All[var:lhs.shape[0]](lhs[var] >= rhs[var]))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x >= y)

    Eq << Eq[0].this.rhs.apply(algebra.all_ge.to.ge.lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
