from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessEqual(abs(x), abs(x - y) + abs(y))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x, y)

    Eq << algebra.imply.le.abs.add.apply(x - y, y)


if __name__ == '__main__':
    run()

