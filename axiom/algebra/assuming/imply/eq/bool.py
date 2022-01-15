from util import *



@apply
def apply(given):
    q, p = given.of(Assuming)

    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, h, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Assuming(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed

    Eq << algebra.infer.imply.eq.bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-01-28
