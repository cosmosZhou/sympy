from util import *


@apply
def apply(self, *, simplify=True):
    function, *limits_d = self.of(Derivative)
    f, *limits_s = function.of(Integral)

    f = Derivative(f, *limits_d)
    if simplify:
        f = f.simplify()
    return Equal(self, Integral(f, *limits_s))


@prove(proved=False)
def prove(Eq):
    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Derivative[x](Integral[y](f(x, y))))


if __name__ == '__main__':
    run()
# created on 2021-07-25
