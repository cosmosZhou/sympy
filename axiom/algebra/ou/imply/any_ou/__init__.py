from util import *

import axiom


@apply
def apply(imply):
    exists = imply.of(Or)
    limits = None

    eqs = []
    for exist in exists:
        if not exist.is_Exists:
            eqs.append(exist)
        else:
            fn, *_limits = exist.args

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

    Eq << apply(Or(Exists[x:A]((g(x) > 0)), f(x) > 0))

    Eq << Eq[0].this.args[0].apply(algebra.cond.imply.any.conditioned, (x, A))

    Eq << algebra.ou.imply.any_ou.distributed.apply(Eq[-1])

if __name__ == '__main__':
    run()

from . import distributed
