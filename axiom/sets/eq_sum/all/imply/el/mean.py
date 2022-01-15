from util import *


@apply
def apply(eq, forall):
    wi, i_limit = eq.of(Equal[Sum, 1])
    (S[wi], (xi, domain)), S[i_limit] = forall.of(All[And[Expr >= 0, Element]])
    i, S[0], n = i_limit

    return Element(Sum[i:n](wi * xi), domain)

@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True)
    w, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & Element(x[i], Interval(a, b))))

    Eq << sets.imply.infer.el.interval.apply(Eq[1].find(Element), w=w[:n])

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-05-31
