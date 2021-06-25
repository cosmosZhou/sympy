from util import *


@apply
def apply(x, n=None):
    if n is None:
        n = x.generate_var(integer=True)
    assert x.is_real
    return Any[n](Contains(n, Interval(x - 1, x, left_open=True)))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True)
    n = Symbol.n(integer=True)
    Eq << apply(x, n)

    Eq << Eq[-1].this.function.apply(sets.contains.given.et.split.interval)

    Eq << Eq[-1].this.find(Greater) + 1

    Eq << Eq[-1].this.function.apply(sets.et.given.contains.st.le_gt)
    
    Eq << sets.imply.any_contains.real.apply(x, n)


if __name__ == '__main__':
    run()

