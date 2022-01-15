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
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})) & Equal(Card(S), n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k, n = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer * k, given=True)
    Eq << apply(Equal(Card(S), n))

    Eq << sets.eq.imply.any_eq.condset.eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True, simplify=None, ret=0)


if __name__ == '__main__':
    run()
# created on 2021-02-02
