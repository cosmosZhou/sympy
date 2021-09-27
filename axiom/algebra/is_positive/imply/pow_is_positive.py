from util import *


@apply
def apply(given, n):    
    x = given.of(Expr > 0)
    assert n.is_integer and n > 0
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x > 0, n)

    Eq << Eq[1].subs(n, 1)

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Suffice(Eq[1], Eq.induct, plausible=True)
    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq[0], Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()