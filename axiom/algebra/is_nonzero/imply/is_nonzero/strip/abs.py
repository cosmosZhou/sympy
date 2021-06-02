from util import *
import axiom



@apply
def apply(given):
    x = given.of(Unequal[0])
    x = x.of(Abs)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)

    Eq << apply(Unequal(abs(a), 0))

    Eq << ~Eq[1]

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[0])

if __name__ == '__main__':
    run()
