from util import *



@apply
def apply(given):
    x = given.of(Unequal[0])
    x = x.of(Abs)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol(real=True, given=True)

    Eq << apply(Unequal(abs(a), 0))

    Eq << ~Eq[1]

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
# created on 2018-03-19
# updated on 2018-03-19
