from util import *


@apply
def apply(imply):
    exists = imply.of(Or)
    limits = None
    eqs = []
    for exist in exists:
        fn, *_limits = exist.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Any(Or(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(Any[x:A]((g(x) > 0)), Any[x:A](f(x) > 0)))

    Eq << algebra.any_ou.given.ou.any.apply(Eq[1])


if __name__ == '__main__':
    run()

