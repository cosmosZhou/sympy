from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Abs])
    assert n > 0
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
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})) & Equal(abs(S), n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k, given=True)
    Eq << apply(Equal(abs(S), n))

    Eq << sets.eq.imply.any_eq.condset.eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.cond.cond.imply.et, algebra.eq.cond.imply.cond.subs, reverse=True, simplify=None)


if __name__ == '__main__':
    run()