from util import *


@apply
def apply(given, index=-1):
    from axiom.algebra.et.imply.et import split
    return split(given, index)


@prove
def prove(Eq):
    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)))

    Eq <<= Eq[1] & Eq[2]

    
    


if __name__ == '__main__':
    run()


from . import split
from . import collect
from . import mul
from . import subs
from . import transit
# created on 2018-01-16
# updated on 2021-11-24