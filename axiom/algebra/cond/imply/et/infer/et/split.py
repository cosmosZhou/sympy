from util import *


@apply(simplify=False)
def apply(given, *, cond=None):
    assert cond.is_bool
    return Infer(cond, given & cond), Infer(cond.invert(), given & cond.invert())


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(f(e) > 0, cond=e > 0)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=e > 0)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-2])
    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-18
