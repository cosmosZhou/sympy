from util import *


@apply
def apply(self):
    z = self.of(Abs)
    x = re(z)
    y = im(z)
    return Equal(self, sqrt(x * x + y * y))


@prove(provable=False)
def prove(Eq):
    z = Symbol.z(complex=True)
    Eq << apply(abs(z))


if __name__ == '__main__':
    run()
    
