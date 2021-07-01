from util import *


def convert(self):
    [*args] = self.of(Mul)
    for i, arg in enumerate(args):
        if arg.is_Add: 
            summand = []
            for e in arg.args:
                _args = [*args]
                _args[i] = e 
                summand.append(Mul(*_args))
            return Add(*summand).simplify()
                
@apply
def apply(self):
    rhs = convert(self)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(complex=True)
    a = Symbol.a(complex=True)
    b = Symbol.b(complex=True)
    Eq << apply(x * (a + b))

    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    run()

from . import st, square