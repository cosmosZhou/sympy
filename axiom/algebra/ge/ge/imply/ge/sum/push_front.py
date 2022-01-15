from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push_front import absorb_front
    return absorb_front(Sum, GreaterEqual, *imply)


@prove
def prove(Eq):
    from axiom import algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(integer=True)
    Eq << apply((g(a - 1) >= f(a - 1)), Sum[k:a:b](g(k)) >= Sum[k:a:b](f(k)))

    Eq << algebra.ge.ge.imply.ge.add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(algebra.sum.to.add.split, cond={a - 1})

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={a - 1})


if __name__ == '__main__':
    run()

# created on 2019-05-19
