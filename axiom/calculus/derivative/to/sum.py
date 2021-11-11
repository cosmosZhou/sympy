from util import *



@apply
def apply(self):
    function, *limits_d = self.of(Derivative)
    f, *limits_s = function.of(Sum)
    
    return Equal(self, Sum(Derivative(f, *limits_d).doit(), *limits_s))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True)
    f = Function(real=True)
    n = Symbol(integer=True)
    Eq << apply(Derivative[x](Sum[n:0:oo](f[n](x))))


if __name__ == '__main__':
    run()

# created on 2020-10-17
# updated on 2020-10-17
