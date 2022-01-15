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
    a, b, c, d = Symbol(real=True)
    Eq << apply(Equal(Matrix([a, b]), Matrix([c, d])))



    Eq << Eq[0] @ Matrix([0, 1])

    Eq << Eq[0] @ Matrix([1, 0])


if __name__ == '__main__':
    run()

# created on 2021-08-03
