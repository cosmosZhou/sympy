from util import *



@apply
def apply(*given):
    is_imply_P, is_imply_Q = given
    p, q = is_imply_P.of(Suffice)
    _q, r = is_imply_Q.of(Suffice)
    if q != _q:
        p, q, _q, r = _q, r, p, q

    assert q == _q
    return Suffice(p, r)


@prove
def prove(Eq):
    from axiom import algebra
    p = Symbol.p(real=True, given=True)
    q = Symbol.q(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Suffice(p > q, x > y), Suffice(x > y, a > b))

    Eq << Eq[0].apply(algebra.suffice.imply.ou)

    Eq << Eq[1].apply(algebra.suffice.imply.ou)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[2].apply(algebra.suffice.given.ou)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[-3]

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()
