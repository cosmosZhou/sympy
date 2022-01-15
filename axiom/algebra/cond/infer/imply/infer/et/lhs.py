from util import *


@apply
def apply(cond, suffice):
    p, q = suffice.of(Infer)
    return Infer(p & cond, q)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(integer=True, given=True)


    f, g = Function(real=True)

    Eq << apply(a > b, Infer(x > y, f(x) > g(y)))

    Eq << algebra.infer.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1])

    Eq << algebra.infer.imply.ou.apply(Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-22
