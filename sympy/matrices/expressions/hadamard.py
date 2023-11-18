from sympy.core import Mul, sympify
from sympy.matrices.expressions.matexpr import MatrixExpr, Identity, OneMatrix, ZeroMatrix
from ..common import ShapeError
from sympy.strategies import unpack, flatten, condition, exhaust, do_one, rm_id, sort
from sympy.core.cache import cacheit


def hadamard_product(*matrices):
    """
    Return the elementwise (aka Hadamard) product of matrices.

    Examples
    ========

    >>> from sympy.matrices import hadamard_product, MatrixSymbol
    >>> A = MatrixSymbol('A', 2, 3)
    >>> B = MatrixSymbol('B', 2, 3)
    >>> hadamard_product(A)
    A
    >>> hadamard_product(A, B)
    A.*B
    >>> hadamard_product(A, B)[0, 1]
    A[0, 1]*B[0, 1]
    """
    if not matrices:
        raise TypeError("Empty Hadamard product is undefined")
    validate(*matrices)
    if len(matrices) == 1:
        return matrices[0]
    else:
        matrices = [i for i in matrices if not i.is_Identity]
        return HadamardProduct(*matrices).doit()


class HadamardProduct(MatrixExpr):
    """
    Elementwise product of matrix expressions

    Examples
    ========

    Hadamard product for matrix symbols:

    >>> from sympy.matrices import hadamard_product, HadamardProduct, MatrixSymbol
    >>> A = MatrixSymbol('A', 5, 5)
    >>> B = MatrixSymbol('B', 5, 5)
    >>> isinstance(hadamard_product(A, B), HadamardProduct)
    True

    Notes
    =====

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the product, use the function
    ``hadamard_product()`` or ``HadamardProduct.doit``
    """
    is_HadamardProduct = True

    def __new__(cls, *args, **kwargs):
        args = list(map(sympify, args))
#         check = kwargs.get('check', True)
#         if check:
#             validate(*args)
        if len(args) == 1:
            return args[0]
        return super(HadamardProduct, cls).__new__(cls, *args)

    @cacheit
    def _eval_shape(self):
        return self.args[0].shape

    def _entry(self, i, j, **kwargs):
        return Mul(*[arg._entry(i, j, **kwargs) for arg in self.args])

    def _eval_transpose(self, axis=-1):
        from sympy.matrices.expressions.transpose import transpose
        return HadamardProduct(*list(map(transpose, self.args)))

    def doit(self, **ignored):
        return canonicalize(self)

    def _eval_derivative_matrix_lines(self, x):
        from sympy.core.expr import ExprBuilder
        from sympy.codegen.array_utils import CodegenArrayDiagonal, CodegenArrayTensorProduct
        from sympy.matrices.expressions.matexpr import _make_matrix

        with_x_ind = [i for i, arg in enumerate(self.args) if arg.has(x)]
        lines = []
        for ind in with_x_ind:
            left_args = self.args[:ind]
            right_args = self.args[ind + 1:]

            d = self.args[ind]._eval_derivative_matrix_lines(x)
            hadam = hadamard_product(*(right_args + left_args))
            diagonal = [(0, 2), (3, 4)]
            diagonal = [e for j, e in enumerate(diagonal) if self.shape[j] != 1]
            for i in d:
                l1 = i._lines[i._first_line_index]
                l2 = i._lines[i._second_line_index]
                subexpr = ExprBuilder(
                    CodegenArrayDiagonal,
                    [
                        ExprBuilder(
                            CodegenArrayTensorProduct,
                            [
                                ExprBuilder(_make_matrix, [l1]),
                                hadam,
                                ExprBuilder(_make_matrix, [l2]),
                            ]
                        ),
                    ] + diagonal,  # turn into *diagonal after dropping Python 2.7

                )
                i._first_pointer_parent = subexpr.args[0].args[0].args
                i._first_pointer_index = 0
                i._second_pointer_parent = subexpr.args[0].args[2].args
                i._second_pointer_index = 0
                i._lines = [subexpr]
                lines.append(i)

        return lines


def validate(*args):
    if not all(arg.is_Matrix for arg in args):
        raise TypeError("Mix of Matrix and Scalar symbols")
    A = args[0]
    for B in args[1:]:
        if A.shape != B.shape:
            raise ShapeError("Matrices %s and %s are not aligned" % (A, B))


# TODO Implement algorithm for rewriting Hadamard product as diagonal matrix
# if matmul identy matrix is multiplied.
def canonicalize(x):
    """Canonicalize the Hadamard product ``x`` with mathematical properties.

    Examples
    ========

    >>> from sympy.matrices.expressions import MatrixSymbol, HadamardProduct
    >>> from sympy.matrices.expressions import OneMatrix, ZeroMatrix
    >>> from sympy.matrices.expressions.hadamard import canonicalize

    >>> A = MatrixSymbol('A', 2, 2)
    >>> B = MatrixSymbol('B', 2, 2)
    >>> C = MatrixSymbol('C', 2, 2)

    Hadamard product associativity:

    >>> X = HadamardProduct(A, HadamardProduct(B, C))
    >>> X
    A.*(B.*C)
    >>> canonicalize(X)
    A.*B.*C

    Hadamard product commutativity:

    >>> X = HadamardProduct(A, B)
    >>> Y = HadamardProduct(B, A)
    >>> X
    A.*B
    >>> Y
    B.*A
    >>> canonicalize(X)
    A.*B
    >>> canonicalize(Y)
    A.*B

    Hadamard product identity:

    >>> X = HadamardProduct(A, OneMatrix(2, 2))
    >>> X
    A.*1
    >>> canonicalize(X)
    A

    Absorbing element of Hadamard product:

    >>> X = HadamardProduct(A, ZeroMatrix(2, 2))
    >>> X
    A.*0
    >>> canonicalize(X)
    0

    Rewriting to Hadamard Power

    >>> X = HadamardProduct(A, A, A)
    >>> X
    A.*A.*A
    >>> canonicalize(X)
    A.**3

    Notes
    =====

    As the Hadamard product is associative, nested products can be flattened.

    The Hadamard product is commutative so that factors can be sorted for
    canonical form.

    A matrix of only ones is an identity for Hadamard product,
    so every matrices of only ones can be removed.

    Any zero matrix will make the whole product a zero matrix.

    Duplicate elements can be collected and rewritten as HadamardPower

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Hadamard_product_(matrices)
    """
    from sympy.core.compatibility import default_sort_key

    # Associativity
    rule = condition(
            lambda x: isinstance(x, HadamardProduct),
            flatten
        )
    fun = exhaust(rule)
    x = fun(x)

    # Identity
    fun = condition(
            lambda x: isinstance(x, HadamardProduct),
            rm_id(lambda x: isinstance(x, OneMatrix))
        )
    x = fun(x)

    # Absorbing by Zero Matrix
    def absorb(x):
        if any(isinstance(c, ZeroMatrix) for c in x.args):
            return ZeroMatrix(*x.shape)
        else:
            return x

    fun = condition(
            lambda x: isinstance(x, HadamardProduct),
            absorb
        )
    x = fun(x)

    # Rewriting with HadamardPower
    if isinstance(x, HadamardProduct):
        from collections import Counter
        tally = Counter(x.args)

        new_arg = []
        for base, exp in tally.items():
            if exp == 1:
                new_arg.append(base)
            else:
                new_arg.append(HadamardPower(base, exp))

        x = HadamardProduct(*new_arg)

    # Commutativity
    fun = condition(
            lambda x: isinstance(x, HadamardProduct),
            sort(default_sort_key)
        )
    x = fun(x)

    # Unpacking
    x = unpack(x)
    return x


def hadamard_power(base, exp):
    base = sympify(base)
    exp = sympify(exp)
    if exp == 1:
        return base
    if not base.is_Matrix:
        return base ** exp
    if exp.is_Matrix:
        raise ValueError("cannot raise expression to a matrix")
    return HadamardPower(base, exp)


class HadamardPower(MatrixExpr):
    """
    Elementwise power of matrix expressions
    """

    def __new__(cls, base, exp):
        base = sympify(base)
        exp = sympify(exp)
        obj = super(HadamardPower, cls).__new__(cls, base, exp)
        return obj

    @property
    def base(self):
        return self._args[0]

    @property
    def exp(self):
        return self._args[1]

    def _eval_shape(self):
        return self.base.shape

    def _entry(self, i, j, **kwargs):
        return self.base._entry(i, j, **kwargs) ** self.exp

    def _eval_transpose(self, axis=-1):
        from sympy.matrices.expressions.transpose import transpose
        return HadamardPower(transpose(self.base), self.exp)

    def _eval_derivative_matrix_lines(self, x):
        from sympy.codegen.array_utils import CodegenArrayTensorProduct
        from sympy.codegen.array_utils import CodegenArrayContraction, CodegenArrayDiagonal
        from sympy.core.expr import ExprBuilder
        from sympy.matrices.expressions.matexpr import _make_matrix

        lr = self.base._eval_derivative_matrix_lines(x)
        for i in lr:
            diagonal = [(1, 2), (3, 4)]
            diagonal = [e for j, e in enumerate(diagonal) if self.base.shape[j] != 1]
            l1 = i._lines[i._first_line_index]
            l2 = i._lines[i._second_line_index]
            subexpr = ExprBuilder(
                CodegenArrayDiagonal,
                [
                    ExprBuilder(
                        CodegenArrayTensorProduct,
                        [
                            ExprBuilder(_make_matrix, [l1]),
                            self.exp * hadamard_power(self.base, self.exp - 1),
                            ExprBuilder(_make_matrix, [l2]),
                        ]
                    ),
                ] + diagonal,  # turn into *diagonal after dropping Python 2.7
                validator=CodegenArrayDiagonal._validate
            )
            i._first_pointer_parent = subexpr.args[0].args[0].args
            i._first_pointer_index = 0
            i._first_line_index = 0
            i._second_pointer_parent = subexpr.args[0].args[2].args
            i._second_pointer_index = 0
            i._second_line_index = 0
            i._lines = [subexpr]
        return lr
