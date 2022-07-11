from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Card])
    assert n > 0
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]:Equal(Card(x[:n].cup_finiteset()), n)](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n, k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer * k, given=True)
    Eq << apply(Equal(Card(S), n))

    Eq << sets.imply.all_any_eq.apply(n, etype=S.etype, elements=Eq[-1].variable)

    Eq.ou = algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, S)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq.ou)

    Eq << Eq[-1].this.limits[0][1].apply(sets.all_ne.imply.eq.card.cup.finiteset)


if __name__ == '__main__':
    run()
# created on 2021-02-02
