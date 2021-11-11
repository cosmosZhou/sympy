from util import *



@apply
def apply(given):
    p, q = given.of(Infer)
    return q


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Infer(x > y, f(x) > g(y)))

    Eq << Eq[0].this.apply(algebra.infer.to.ou)

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# created on 2019-06-30
# updated on 2019-06-30
