from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    x, p = is_imply_P.of(Infer)
    y, q = is_imply_Q.of(Infer)

    return Infer(x & y, p & q)


@prove
def prove(Eq):
    from axiom import algebra

    p0, p1, q0, q1 = Symbol(bool=True)
    Eq << apply(Infer(p0, q0), Infer(p1, q1))

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Infer(p0 & p1, p0, plausible=True), Infer(p0 & p1, p1, plausible=True)

    Eq <<= algebra.infer.infer.imply.infer.transit.apply(Eq[0], Eq[-2]), algebra.infer.infer.imply.infer.transit.apply(Eq[1], Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2018-02-02
# updated on 2022-01-27
