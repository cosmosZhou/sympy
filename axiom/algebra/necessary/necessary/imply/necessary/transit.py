from util import *



@apply
def apply(is_imply_P, is_imply_Q):
    p, q = is_imply_P.of(Necessary)
    _q, r = is_imply_Q.of(Necessary)
    if q != _q:
        p, q, _q, r = _q, r, p, q

    assert q == _q
    return Necessary(p, r)


@prove
def prove(Eq):
    from axiom import algebra
    p, q, x, y, a, b = Symbol(real=True, given=True)

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
