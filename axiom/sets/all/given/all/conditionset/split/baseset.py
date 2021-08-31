from util import *


@apply
def apply(imply, s):
    function, (x, cond, baseset) = imply.of(All)
    assert s.is_Symbol
    __x, (_x, _cond, _baseset) = s.definition.of(Cup[FiniteSet])
    assert x == _x == __x
    assert _cond == cond
    assert _baseset == baseset

    return All[x:s](function)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    S = Symbol(etype=dtype.complex * n)
    f, g = Function(shape=(), integer=True)

    s = Symbol(conditionset(x, Equal(f(x), 1), S))
    Eq << apply(All[x: Equal(f(x), 1):S](Equal(g(x), 1)), s)

    Eq << Eq[-1].this.limits[0][1].definition


if __name__ == '__main__':
    run()
