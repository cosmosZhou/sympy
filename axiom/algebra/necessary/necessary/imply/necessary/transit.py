from util import *
import axiom



@apply
def apply(*given):
    is_imply_P, is_imply_Q = given
    p, q = is_imply_P.of(Necessary)
    _q, r = is_imply_Q.of(Necessary)
    if q != _q:
        p, q, _q, r = _q, r, p, q

    assert q == _q
    return Necessary(p, r)


@prove
def prove(Eq):
    from axiom import algebra
    p = Symbol.p(real=True, given=True)
    q = Symbol.q(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Necessary(p > q, x > y), Necessary(x > y, a > b))

    Eq << Eq[0].apply(algebra.necessary.imply.ou)

    Eq << Eq[1].apply(algebra.necessary.imply.ou)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)

    Eq << Eq[2].apply(algebra.necessary.given.ou)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[-3]

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()
