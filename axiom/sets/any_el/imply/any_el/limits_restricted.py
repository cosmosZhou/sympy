from util import *


@apply
def apply(given):
    (_x, S), (x,), *limits = given.of(Any[Element])
    assert x == _x
    return Any(Element(x, S), (x, S), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol(etype=dtype.real, given=True)
    e, t = Symbol(real=True)

    Eq << apply(Any[e, t:S](Element(e, S - {t})))

    Eq << Eq[-1].simplify()

    Eq << ~Eq[-1]

    Eq << sets.any_el.imply.ne_empty.apply(Eq[0], simplify=None)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (t, S))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << algebra.eq.ne.imply.ne.subs.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()

# created on 2020-07-14
# updated on 2020-07-14
