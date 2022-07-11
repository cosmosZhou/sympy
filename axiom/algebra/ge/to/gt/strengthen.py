from util import *


@apply(given=None)
def apply(ge):
    a, x = ge.of(GreaterEqual)
    x -= 1
    assert x.is_integer and a.is_integer
    
    return Equivalent(ge, Greater(a, x).simplify(), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x >= a + 1)

    Eq << Eq[0].this.rhs.apply(algebra.gt.to.ge.strengthen)


if __name__ == '__main__':
    run()
# created on 2022-01-28
