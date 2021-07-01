from util import *


@apply
def apply(given, P):
    f_gx, *limits = given.of(All)
    assert P.is_ConditionSet or P.definition.is_ConditionSet
    _, y, cond = P.image_set()
    pattern = cond._subs(y, Wild(y.name, **y.assumptions0), symbol=False)
    
    res = f_gx.match(pattern)
    gx, *_ = res.values()

    return given.func(Contains(gx, P), *limits)


@prove
def prove(Eq): 
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(m,))
    A = Symbol.A(etype=dtype.complex * n)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(m,))
    
    P = Symbol.P(conditionset(y, Equal(f(y), 1)))
    Eq << apply(All[x:A](Equal(f(g(x)), 1)), P)
    
    Eq << Eq[-1].this.function.rhs.definition


if __name__ == '__main__':
    run()
