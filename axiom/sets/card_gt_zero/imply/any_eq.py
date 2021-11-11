from util import *


@apply
def apply(given, x=None):
    S = given.of(Card > 0)
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
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer * k, given=True)
    Eq << apply(Card(s) > 0)

    Eq << sets.gt.imply.el.range.apply(Eq[0])

    m = Symbol(domain=Range(1, oo))
    Eq << sets.el.imply.any_eq.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.any_et, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True, simplify=None, ret=1)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()
# created on 2021-02-03
# updated on 2021-02-03
