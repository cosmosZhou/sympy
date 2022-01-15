from util import *


@apply(simplify=False)
def apply(suffice, *, cond=None):
    cond = sympify(cond)
    lhs, fy = suffice.of(Infer)
    return Infer(cond & lhs, fy), cond


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Infer(Equal(a, 0), Equal(c, 0)), cond=Equal(b, 0))

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-15
