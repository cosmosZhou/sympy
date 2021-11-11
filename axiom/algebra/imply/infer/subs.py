from util import *



@apply(given=None)
def apply(given, old, new):
    assert old.is_symbol
    assert not old.is_given
    assert new in given.domain_defined(old)
    return Infer(given, given._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g, t = Function(shape=(), real=True)
    x = Symbol(real=True)

    Eq << apply(Equal(f[n](x), g[n](x)), x, t(x))

    Eq << Eq[0].this.lhs.apply(algebra.eq.imply.eq.subs, x, t(x))


if __name__ == '__main__':
    run()
# created on 2019-03-21
# updated on 2019-03-21
