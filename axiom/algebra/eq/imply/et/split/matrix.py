from util import *


@apply
def apply(given, index=-1):
    lhs, rhs = given.of(Equal)

    assert lhs.is_Matrix and rhs.is_Matrix
    assert len(lhs._args) == len(rhs._args)

    first = Equal(Matrix(lhs._args[:index]), Matrix(rhs._args[:index])).simplify()
    second = Equal(Matrix(lhs._args[index:]), Matrix(rhs._args[index:])).simplify()
    
    return first, second


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    Eq << apply(Equal(Matrix([a, b]), Matrix([c, d])))

    

    Eq << Eq[0] @ Matrix([0, 1])

    Eq << Eq[0] @ Matrix([1, 0])


if __name__ == '__main__':
    run()

