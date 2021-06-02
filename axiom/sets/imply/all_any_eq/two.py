from util import *

# given: A != {}
# Exists[x] (x in A)


@apply
def apply(x=None, y=None, **kwargs):
    if 'etype' in kwargs:
        etype = kwargs['etype']
        S = Symbol.S(etype=etype)
    else:
        S = kwargs['set']

    if x is None:
        x = S.generate_var(**S.etype.dict)
    if y is None:
        y = S.generate_var(excludes={x}, **S.etype.dict)

    return ForAll[S:Equal(abs(S), 2)](Exists[x: Unequal(x, y), y](Equal(S, {x, y})))


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)
    Eq << apply(set=S)

    Eq << algebra.imply.all.limits_assert.apply(Eq[0].limits)

    Eq << Eq[-1].this.function.apply(sets.eq.imply.any_eq.two)


if __name__ == '__main__':
    run()

