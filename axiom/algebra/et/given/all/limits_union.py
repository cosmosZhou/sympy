from util import *


@apply
def apply(given):
    from sympy.concrete.limits import limits_union
    all_a, all_b = given.of(And)
    fn, *limits_a = all_a.of(All)
    _fn, *limits_b = all_b.of(All)
    assert fn == _fn
    limits = limits_union(limits_a, limits_b)
    return All(fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(And(All[e:g(e) > 0](f(e) > 0), All[e:g(e) < 0](f(e) > 0)))

    Eq << algebra.all.imply.et.split.apply(Eq[1], cond=g(e) < 0)


if __name__ == '__main__':
    run()

