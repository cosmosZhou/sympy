from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return limits_subs(Any, self, offset)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    m, d = Symbol(integer=True, given=True)
    f = Function(integer=True)
    Eq << apply(Any[n:1:m + 1](f(n) > 0), d)

    Eq << ~Eq[1]

    Eq << algebra.all.imply.all.limits.subs.offset.apply(Eq[-1], -d)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-07-12
# updated on 2018-07-12
