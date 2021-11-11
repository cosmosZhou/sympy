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

    Eq << sets.el.imply.ne_empty.apply(Eq[-1])
    Eq << sets.interval_ne_empty.imply.le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-24
# updated on 2019-09-24
