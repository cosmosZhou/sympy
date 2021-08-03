from util import *


@apply
def apply(given, x=None):
    S, l = given.of(Abs >= Expr)
    assert l > 0
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
    from axiom import algebra, sets

    k = Symbol.k(integer=True, positive=True)
    s = Symbol.s(etype=dtype.integer * k, given=True)
    l = Symbol.l(integer=True, positive=True)
    Eq << apply(abs(s) >= l)

    Eq << algebra.ge.imply.is_positive.apply(Eq[0])

    Eq << sets.abs_is_positive.imply.any_eq.apply(Eq[-1])

    

    

    

    


if __name__ == '__main__':
    run()