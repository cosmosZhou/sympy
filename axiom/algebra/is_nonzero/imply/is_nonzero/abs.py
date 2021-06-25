from util import *



@apply
def apply(given):
    x = given.of(Unequal[0])
    return Unequal(abs(x), 0)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)

    Eq << apply(Unequal(a, 0))

    Eq << Eq[1].this.lhs.apply(algebra.abs.to.piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])



if __name__ == '__main__':
    run()
