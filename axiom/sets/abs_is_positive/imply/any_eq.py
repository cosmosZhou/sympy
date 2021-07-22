from util import *


@apply
def apply(given, x=None):
    S = given.of(Abs > 0)
    n = abs(S)
    i = S.generate_var(integer=True)
    j = S.generate_var(integer=True, excludes={i})
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

    k = Symbol.k(integer=True, positive=True)
    s = Symbol.s(etype=dtype.integer * k, given=True)
    Eq << apply(abs(s) > 0)

    Eq << sets.gt.imply.contains.range.apply(Eq[0])

    m = Symbol.m(domain=Range(1, oo))
    Eq << sets.contains.imply.any_eq.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.any_et, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.cond.cond.imply.et, algebra.eq.eq.imply.eq.subs, swap=True, reverse=True, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()