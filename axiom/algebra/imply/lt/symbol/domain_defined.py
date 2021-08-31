from util import *



@apply
def apply(x):
    assert x.is_Symbol
    domain = x.domain
    domain.is_Interval
    assert domain.left_open or domain.right_open
    return Less(*domain.args)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True)
    domain=Interval(a, b, right_open=True)
    x = Symbol(domain=domain)
    Eq << apply(x)

    Eq << Element(x, domain, plausible=True)

    Eq << sets.el.imply.is_nonempty.apply(Eq[-1])
    Eq << sets.interval_is_nonempty.imply.lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
