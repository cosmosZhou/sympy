from util import *


@apply
def apply(imply):
    exists = imply.of(Or)
    limits = None
    eqs = []
    for exist in exists:
        fn, *_limits = exist.of(Exists)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Exists(Or(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(Exists[x:A]((g(x) > 0)), Exists[x:A](f(x) > 0)))

    Eq << algebra.any_ou.given.ou.any.apply(Eq[1])


if __name__ == '__main__':
    run()

