from util import *


@apply
def apply(given, x=None):
    S = given.of(Unequal[Card, 0])
    n = Card(S)
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from axiom import algebra, sets

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer * k, given=True)
    Eq << apply(Unequal(Card(s), 0))

    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[0])

    Eq << sets.card_is_positive.imply.any_eq.apply(Eq[-1])


if __name__ == '__main__':
    run()