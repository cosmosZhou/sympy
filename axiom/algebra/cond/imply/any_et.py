from util import *


@apply
def apply(given, wrt=None):
    assert given._has(wrt)
    x = given.generate_var(**wrt.type.dict)
    domain = wrt.domain

    return Any[x:domain](given._subs(wrt, x) & Equal(x, wrt))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True, given=True)
    e = Symbol(domain=Range(n), given=True)
    f = Function(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.find(Unequal).apply(sets.ne.imply.notin)

    Eq << Eq[-1].apply(algebra.all_ou.imply.all.limits.absorb, index=1)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2019-02-26
