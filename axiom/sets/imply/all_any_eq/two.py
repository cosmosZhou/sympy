from util import *

# given: A != {}
# Any[x] (x in A)


@apply
def apply(x=None, y=None, **kwargs):
    if 'etype' in kwargs:
        etype = kwargs['etype']
        S = Symbol(etype=etype)
    else:
        S = kwargs['set']

    if x is None:
        x = S.generate_var(**S.etype.dict)
    if y is None:
        y = S.generate_var(excludes={x}, **S.etype.dict)

    return All[S:Equal(Card(S), 2)](Any[x: Unequal(x, y), y](Equal(S, {x, y})))


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer * k)
    Eq << apply(set=S)

    Eq << algebra.imply.all.limits_assert.apply(Eq[0].limits)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.any_eq.two)


if __name__ == '__main__':
    run()

# created on 2020-09-07
