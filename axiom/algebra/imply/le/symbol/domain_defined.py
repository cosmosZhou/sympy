from util import *


@apply
def apply(x):
    assert x.is_Symbol
    domain = x.domain
    domain.is_Interval
    return LessEqual(*domain.args)


@prove
def prove(Eq):
    from axiom import sets
    a, b = Symbol(real=True)
    domain=Interval(a, b)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Element(x, domain, plausible=True)

    Eq << sets.el.imply.is_nonempty.apply(Eq[-1])
    Eq << sets.interval_is_nonempty.imply.le.apply(Eq[-1])


if __name__ == '__main__':
    run()
