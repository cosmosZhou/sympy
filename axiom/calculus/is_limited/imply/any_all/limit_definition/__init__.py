from util import *


def of_limited(given, **kwargs):
    limit, R = given.of(Contains)
    assert R.is_set
    
    expr, *limits = limit.of(Limit)
    if kwargs.get('real'):
        assert R.is_UniversalSet
        return (expr, *limits)
    
    if kwargs.get('nonzero'):
        a, b = R.of(Union)
        assert a.is_Interval and b.is_Interval
        assert a.right_open and b.left_open
        assert a.args == (-oo, 0)
        assert b.args == (0, oo)
        return (expr, *limits)
    
    if kwargs.get('positive'):
        assert R == Interval(0, oo, left_open=True)
        return (expr, *limits)
    
    return (expr, *limits, R)
    

@apply
def apply(given, ε=None, δ=None):
    from axiom.calculus.eq.to.any_all.limit_definition import any_all
    fn, (x, x0, dir) = of_limited(given, real=True)
#     A = given.generate_var(definition=given)

    A = fn.generate_var(excludes={x}, **fn.type.dict)

    cond = any_all(Equal(given.lhs, A), ε, δ)
    return cond._subs(A, given.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets
    n = Symbol.n(integer=True, positive=True)

    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)

    f = Function.f(real=True, shape=())

    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))

    x0 = oo
#     x0 = -oo

    a = Symbol.a(real=True)
#     a = oo
#     a = -oo

    direction = 1

    Eq << apply(Contains(Limit[x:x0:direction](f(x)), Reals))

    Eq << sets.contains.imply.any_eq.apply(Eq[0], var='A')

    Eq << Eq[-1].this.function.apply(calculus.eq.imply.any_all.limit_definition.limit)


if __name__ == '__main__':
    run()

from . import symbol_subs
