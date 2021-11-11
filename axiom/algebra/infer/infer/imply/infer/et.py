from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    x, p = is_imply_P.of(Infer)
    y, q = is_imply_Q.of(Infer)

    return Infer(x & y, p & q)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(Infer(x > 0, a > 0), Infer(y > 0, b > 0))

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Infer((x > 0) & (y > 0), x > 0, plausible=True), Infer((x > 0) & (y > 0), y > 0, plausible=True)

    Eq <<= algebra.infer.infer.imply.infer.transit.apply(Eq[0], Eq[-2]), algebra.infer.infer.imply.infer.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-02-02
# updated on 2018-02-02
