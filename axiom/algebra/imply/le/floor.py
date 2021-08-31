from util import *


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    return LessEqual(Floor(x / d) * d, x, evaluate=evaluate)

@prove
def prove(Eq):
    x = Symbol(real=True)
    d = Symbol(integer=True, positive=True)

    Eq << apply(x, d)

    Eq << Eq[-1] / d


if __name__ == '__main__':
    run()

