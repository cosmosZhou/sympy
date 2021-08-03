from util import *


def convert(self, deep=False):
    [*args] = self.of(Mul)
    for i, arg in enumerate(args):
        if arg.is_Add: 
            summand = []
            for e in arg.args:
                _args = [*args]
                _args[i] = e 
                prod = Mul(*_args)
                if deep and prod.is_Mul:
                    prod = convert(prod, True)
                summand.append(prod)
            return Add(*summand).simplify()
    return self
                
@apply
def apply(self, deep=False):
    rhs = convert(self, deep=deep)
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
del poly
from . import poly
