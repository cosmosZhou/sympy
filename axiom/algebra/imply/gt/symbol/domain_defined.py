from util import *


@apply
def apply(x):
    assert x.is_Symbol
    domain = x.domain
    domain.is_Interval
    assert domain.left_open or domain.right_open
    a, b = domain.args
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    domain=Interval(a, b, right_open=True)
    x = Symbol.x(domain=domain)
    Eq << apply(x)

    Eq << algebra.imply.lt.symbol.domain_defined.apply(x)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()