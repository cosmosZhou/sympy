from util import *


@apply
def apply(given):
    all_a, all_b = given.of(And)
    fn, *limits = all_a.of(ForAll)
    _fn, *_limits = all_b.of(ForAll)
    assert limits == _limits
    return ForAll(fn & _fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)

    Eq << apply(And(ForAll[e:g(e) > 0](f(e) > 0), ForAll[e:g(e) > 0](h(e) > 0)))

    Eq << algebra.all_et.imply.all.apply(Eq[1])

    Eq << algebra.et.given.conds.apply(Eq[0])


if __name__ == '__main__':
    run()

