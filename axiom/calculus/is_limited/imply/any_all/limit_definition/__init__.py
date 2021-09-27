from util import *


def of_limited(given, **kwargs):
    limit, R = given.of(Element)
    assert R.is_set

    expr, *limits = limit.of(Limit)
    if kwargs.get('real'):
        assert R == Interval(-oo, oo)
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

    if kwargs.get('extended_real'):
        assert R in Interval(-oo, oo, left_open=False, right_open=False)
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
    from axiom import sets, calculus

    n = Symbol(integer=True, positive=True)
    x, x0, a = Symbol(real=True)
    #x = Symbol.x(real=True, shape=(n,))
    x = Symbol(integer=True)
    f = Function(real=True, shape=())
    #x0 = Symbol.x0(real=True, shape=(n,))
    x0 = oo
    #x0 = -oo
    #a = oo
    #a = -oo
    direction = 1
    Eq << apply(Element(Limit[x:x0:direction](f(x)), Reals))

    Eq << sets.el.imply.any_eq.apply(Eq[0], var='A')

    Eq << Eq[-1].this.expr.apply(calculus.eq.imply.any_all.limit_definition.limit)


if __name__ == '__main__':
    run()

from . import symbol_subs
