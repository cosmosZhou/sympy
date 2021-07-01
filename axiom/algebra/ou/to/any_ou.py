from util import *


@apply(given=None)
def apply(imply):
    limits = None
    eqs = []
    for exist in imply.of(Or):
        fn, *_limits = exist.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Equivalent(imply, Any(Or(*eqs), *limits))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)

    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(Any[x:A]((g(x) > 0)), Any[x:A](f(x) > 0)))

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.any_ou.given.ou.any)

    Eq << Eq[-1].this.rhs.apply(algebra.any_ou.imply.ou.any)


if __name__ == '__main__':
    run()

