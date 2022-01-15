from util import *


@apply
def apply(given):
    (fx, M), *limits = given.of(All[GreaterEqual])
    return Inf(fx, *limits) >= M


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) >= M))

    Eq << Eq[1].this.lhs.apply(algebra.inf.to.reducedMax)

    m = Symbol(Eq[-1].lhs)
    Eq << m.this.definition

    Eq << algebra.eq_reducedMax.imply.all_ge.apply(Eq[-1])

    y = Eq[-1].variable
    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].subs(y, M)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()
# created on 2019-01-15
