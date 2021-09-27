from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Card])
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
    return Any[x[:n]:All[j:i, i:n](Unequal(x[i], x[j]))](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n, k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer * k, given=True)
    Eq << apply(Equal(Card(S), n))

    Eq << sets.imply.all_any_eq.apply(n, etype=S.etype, elements=Eq[-1].variable)

    Eq.ou = algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, S)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq.ou)


if __name__ == '__main__':
    run()

