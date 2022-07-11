from util import *


@apply
def apply(self):
    args, *limits_d = self.of(Derivative[Mul])
    rhs = Add(*[Derivative(arg, *limits_d) * Mul(*args[:i] + args[i + 1:]) for i, arg in enumerate(args)])
    return Equal(self, rhs)


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Derivative[x](f(x) * g(x)))


if __name__ == '__main__':
    run()
# created on 2022-01-19
