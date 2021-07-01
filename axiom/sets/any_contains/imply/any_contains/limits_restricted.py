from util import *


@apply
def apply(given):
    (_x, S), (x,), *limits = given.of(Any[Contains])
    assert x == _x
    return Any(Contains(x, S), (x, S), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol.S(etype=dtype.real, given=True)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)

    Eq << apply(Any[e, t:S](Contains(e, S // {t})))

    Eq << Eq[-1].simplify()

    Eq << ~Eq[-1]

    Eq << sets.any_contains.imply.is_nonemptyset.apply(Eq[0], simplify=None)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (t, S))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << algebra.eq.ne.imply.ne.subs.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()

