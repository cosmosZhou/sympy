from util import *


@apply(given=None)
def apply(lt, var=None):
    lhs, rhs = lt.of(Less)
    assert lhs.shape
    if var is None:
        var = lt.generate_var(integer=True)
    return Equivalent(lt, All[var:lhs.shape[0]](lhs[var] < rhs[var]))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(x < y)

    Eq << Eq[0].this.rhs.apply(algebra.all_lt.to.lt.lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
