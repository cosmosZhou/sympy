from util import *


def transposition(Equal, given, index=-1, left=True):
    lhs, rhs = given.of(Equal)
    if left:
        [*lhs] = lhs.of(Add)
        x = lhs.pop(index)
        lhs = Add(*lhs)
        rhs -= x
    else:
        [*rhs] = rhs.of(Add)
        x = rhs.pop(index)
        rhs = Add(*rhs)
        lhs -= x

    return Equal(lhs, rhs, evaluate=False)

    
@apply(given=None)
def apply(given, index=-1, left=True): 
    return Equivalent(given, transposition(Equal, given, index=index, left=left), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    Eq << apply(Equal(x + a, y))
    
    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
