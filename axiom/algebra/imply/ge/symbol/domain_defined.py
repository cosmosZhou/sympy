from util import *


@apply
def apply(x):
    assert x.is_Symbol
    domain = x.domain
    domain.is_Interval
    a, b = domain.args
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    domain=Interval(a, b)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << algebra.imply.le.symbol.domain_defined.apply(x)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
