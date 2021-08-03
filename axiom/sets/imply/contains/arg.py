from util import *


@apply(simplify=False)
def apply(self):    
    return Contains(Arg(self), Interval(-S.Pi, S.Pi, left_open=True))


@prove
def prove(Eq):
    z = Symbol(complex=True)
    Eq << apply(z)
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()