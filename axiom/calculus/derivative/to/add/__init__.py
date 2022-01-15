from util import *


@apply
def apply(self):
    function, *limits_d = self.of(Derivative)
    args = function.of(Add)

    return Equal(self, Add(*(Derivative(arg, *limits_d).doit() for arg in args)))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) + g(x)))


if __name__ == '__main__':
    run()

from . import Leibneiz
# created on 2020-04-20
