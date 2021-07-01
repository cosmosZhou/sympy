from util import *


@apply
def apply(given, axiom, *args, **kwargs):
    eq = axiom.apply(given, *args, **kwargs)
    assert eq.given is given
    return eq, given


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    axiom = algebra.eq.imply.eq.floor
    Eq << apply(Equal(a, b), axiom)

    Eq << algebra.eq.imply.eq.floor.apply(Eq[0])


if __name__ == '__main__':
    run()

