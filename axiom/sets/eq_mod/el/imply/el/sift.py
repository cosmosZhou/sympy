from util import *


@apply
def apply(eq_mod, contains):
    (x, m), d = eq_mod.of(Equal[Mod])
    S[x], args = contains.of(Element[FiniteSet])

    deletes = set()
    for a in args:
        if Equal(a % m, d) == False:
            deletes.add(a)
    assert deletes
    s = {*args} - deletes

    return Element(x, s)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(integer=True)
    Eq << apply(Equal(x % 3, 1), Element(x, {-2, -1, 0, 1, 2}))

    Eq << sets.el.imply.ou.split.finiteset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.args[0].apply(algebra.eq.eq.imply.eq.subs, swap=True, simplify=None)

    Eq << Eq[-1].this.args[-1].apply(algebra.eq.eq.imply.eq.subs, swap=True, simplify=None)

    Eq << Eq[-1].this.args[1].apply(algebra.eq.eq.imply.eq.subs, swap=True)

    Eq << algebra.et.imply.cond.apply(Eq[-1], 1)

    Eq << sets.ou_eq.imply.el.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-11-19
