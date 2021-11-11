from util import *


@apply
def apply(all_le):
    (fx, M), *limits = all_le.of(All[LessEqual])
    return Sup(fx, *limits) <= M


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(All[x:S](f(x) <= M))

    Eq << Eq[1].this.lhs.apply(algebra.sup.to.reducedMin)

    m = Symbol(Eq[-1].lhs)
    Eq << m.this.definition

    Eq << algebra.eq_reducedMin.imply.all_le.apply(Eq[-1])

    y = Eq[-1].variable
    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].subs(y, M)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].this.lhs.definition


if __name__ == '__main__':
    run()
# created on 2019-01-17
# updated on 2019-01-17
