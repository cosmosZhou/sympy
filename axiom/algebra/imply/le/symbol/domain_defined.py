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
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    domain=Interval(a, b)
    x = Symbol.x(domain=domain)
    Eq << apply(x)
    
    Eq << Contains(x, domain, plausible=True)
    
    Eq << sets.contains.imply.is_nonemptyset.apply(Eq[-1])
    Eq << sets.interval_is_nonemptyset.imply.le.apply(Eq[-1])


if __name__ == '__main__':
    run()