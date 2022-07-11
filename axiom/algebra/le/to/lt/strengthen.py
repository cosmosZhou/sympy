from util import *


@apply(given=None)
def apply(lt):
    x, a = lt.of(LessEqual)
    x -= 1
    assert x.is_integer and a.is_integer
    return Equivalent(lt, Less(x, a).simplify(), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x + 1 <= a)

    Eq << Eq[-1].this.rhs.apply(algebra.lt.to.le.strengthen)
    


if __name__ == '__main__':
    run()
# created on 2022-01-28
