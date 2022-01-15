from util import *



@apply
def apply(self):
    sgm, *limits_d = self.of(Derivative)
    f, *limits_s = sgm.of(Sum)
    for var, *_ in limits_s:
        for x, n in limits_d:
            if x._has(var):
                break
        else:
            continue
        print(sgm)
        print(self)
        raise "var in summation should not appear in derivative"

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
