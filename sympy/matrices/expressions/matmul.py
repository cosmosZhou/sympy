from __future__ import print_function, division

from sympy import Number
from sympy.core import Mul, Basic, sympify
from sympy.core.compatibility import range
from sympy.functions import adjoint
from sympy.matrices.expressions.transpose import transpose
from sympy.strategies import (rm_id, unpack, typed, flatten, exhaust,
        do_one, new)
from sympy.matrices.expressions.matexpr import (MatrixExpr, ShapeError,
        Identity, ZeroMatrix, GenericIdentity, VConcatenate, HConcatenate)
from sympy.matrices.expressions.matpow import MatPow
from sympy.matrices.matrices import MatrixBase


# XXX: MatMul should perhaps not subclass directly from Mul
class MatMul(MatrixExpr, Mul):
    precedence = 45
    """
    A product of matrix expressions

    Examples
    ========

    >>> from sympy import MatMul, MatrixSymbol
    >>> A = MatrixSymbol('A', 5, 4)
    >>> B = MatrixSymbol('B', 4, 3)
    >>> C = MatrixSymbol('C', 3, 6)
    >>> MatMul(A, B, C)
    A*B*C
    """
    is_MatMul = True
    is_Mul = False
    is_commutative = True

    identity = GenericIdentity()

    def __new__(cls, *args, **kwargs):
#         check = kwargs.get('check', True)
        check = kwargs.get('check', False)

        if not args:
            return cls.identity

        if len(args) == 1:
            return args[0]

        # This must be removed aggressively in the constructor to avoid
        # TypeErrors from GenericIdentity().shape
        args = filter(lambda i: cls.identity != i, args)
        args = list(map(sympify, args))
        obj = Basic.__new__(cls, *args)
        factor, matrices = obj.as_coeff_matrices()
        if check:
            validate(*matrices)
        if not matrices:
            # Should it be
            #
            # return Basic.__neq__(cls, factor, GenericIdentity()) ?
            return factor
        return obj

    @property
    def shape(self):
        dimension = self.args[self.argmax_shape()].shape        
        dimension = dimension[:-2]
        for m in self.args:
            if len(m.shape) >= 2:
                dimension += (m.shape[-2],) 
                break
            if len(m.shape) == 1:
                break
        
        last_shape = self.args[-1].shape
        if len(last_shape) > 1:
            dimension += (last_shape[-1],)
        
        return dimension

#         matrices = [arg for arg in self.args if arg.is_Matrix]
#         return (matrices[0].rows, matrices[-1].cols)
    @property
    def dtype(self):
        return self.args[0].dtype[self.args[0].shape] * self.shape

    def _entry(self, i, j=None, expand=True, **kwargs):
        if j is None:
            return self.args[0][i] @ self.func(*self.args[1:])            
                
        from sympy import Dummy, Sum, ImmutableMatrix, Integer

        coeff, matrices = self.as_coeff_matrices()

        if len(matrices) == 1:  # situation like 2*X, matmul is just X
            return coeff * matrices[0][i, j]

        indices = [None] * (len(matrices) + 1)
        ind_ranges = [None] * (len(matrices) - 1)
        indices[0] = i
        indices[-1] = j

        def f():
            counter = 1
            while True:
                yield Dummy("i_%i" % counter)
                counter += 1

        dummy_generator = kwargs.get("dummy_generator", f())

        for i in range(1, len(matrices)):
            indices[i] = next(dummy_generator)

        for i, arg in enumerate(matrices[:-1]):
            ind_ranges[i] = arg.shape[1] - 1
        matrices = [arg._entry(indices[i], indices[i + 1], dummy_generator=dummy_generator) for i, arg in enumerate(matrices)]
        expr_in_sum = Mul.fromiter(matrices)
        if any(v.has(ImmutableMatrix) for v in matrices):
            expand = True
        result = coeff * Sum(
                expr_in_sum,
                *zip(indices[1:-1], [0] * len(ind_ranges), ind_ranges)
            )

        # Don't waste time in result.doit() if the sum bounds are symbolic
        if not any(isinstance(v, (Integer, int)) for v in ind_ranges):
            expand = False
        return result.doit() if expand else result

    def as_coeff_matrices(self):
#         scalars = [x for x in self.args if not x.is_Matrix]
#         matrices = [x for x in self.args if x.is_Matrix]
        scalars = [x for x in self.args if not x.shape]
        matrices = [x for x in self.args if x.shape]

        coeff = Mul(*scalars)
        if coeff.is_commutative is False:
            raise NotImplementedError("noncommutative scalars in MatMul are not supported.")

        return coeff, matrices

    def as_coeff_mmul(self):
        coeff, matrices = self.as_coeff_matrices()
        return coeff, MatMul(*matrices)

    def _eval_transpose(self):
        """Transposition of matrix multiplication.

        Notes
        =====

        The following rules are applied.

        Transposition for matrix multiplied with another matrix:
        `\\left(A B\\right)^{T} = B^{T} A^{T}`

        Transposition for matrix multiplied with scalar:
        `\\left(c A\\right)^{T} = c A^{T}`

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Transpose
        """
        coeff, matrices = self.as_coeff_matrices()
        return MatMul(
            coeff, *[transpose(arg) for arg in matrices[::-1]]).doit()

    def _eval_adjoint(self):
        return MatMul(*[adjoint(arg) for arg in self.args[::-1]]).doit()

    def _eval_trace(self):
        factor, mmul = self.as_coeff_mmul()
        if factor != 1:
            from .trace import trace
            return factor * trace(mmul.doit())
        else:
            raise NotImplementedError("Can't simplify any further")

    def _eval_determinant(self):
#         from sympy.matrices.expressions.determinant import Determinant
        from sympy import det
        factor, matrices = self.as_coeff_matrices()
        square_matrices = only_squares(*matrices)
        return factor ** self.rows * Mul(*list(map(det, square_matrices)))

    def _eval_inverse(self):
        try:
            from sympy.concrete.expr_with_limits import Ref
            return MatMul(*[
                arg.inverse() if isinstance(arg, (MatrixExpr, Ref)) else arg ** -1
                    for arg in self.args[::-1]]).doit()
        except ShapeError:
            from sympy.matrices.expressions.inverse import Inverse
            return Inverse(self)

    def doit(self, **kwargs):
        deep = kwargs.get('deep', True)
        if deep:
            args = [arg.doit(**kwargs) for arg in self.args]
        else:
            args = self.args
        # treat scalar*MatrixSymbol or scalar*MatPow separately
        expr = canonicalize(MatMul(*args))
        return expr

    # Needed for partial compatibility with Mul
    def args_cnc(self, **kwargs):
        coeff_c = [x for x in self.args if x.is_commutative]
        coeff_nc = [x for x in self.args if not x.is_commutative]
        return [coeff_c, coeff_nc]

    def _eval_derivative_matrix_lines(self, x):
        from .transpose import Transpose
        with_x_ind = [i for i, arg in enumerate(self.args) if arg.has(x)]
        lines = []
        for ind in with_x_ind:
            left_args = self.args[:ind]
            right_args = self.args[ind + 1:]

            if right_args:
                right_mat = MatMul.fromiter(right_args)
            else:
                right_mat = Identity(self.shape[1])
            if left_args:
                left_rev = MatMul.fromiter([Transpose(i).doit() if i.is_Matrix else i for i in reversed(left_args)])
            else:
                left_rev = Identity(self.shape[0])

            d = self.args[ind]._eval_derivative_matrix_lines(x)
            for i in d:
                i.append_first(left_rev)
                i.append_second(right_mat)
                lines.append(i)

        return lines

    def simplifier(self):
        from sympy import exp
        if len(self.args) == 2 and all(isinstance(arg, exp) for arg in self.args):
            if len(self.args[0].shape) < len(self.args[1].shape):
                from sympy.concrete import summations
                return summations.Sum(exp(self.args[0].arg + self.args[1].arg.T))
        return self

    def expand(self, free_symbol=None, deep=True):
        from sympy.concrete.expr_with_limits import Ref
        from sympy.concrete.summations import Sum
        if len(self.args) == 2:
            A, B = self.args

            if isinstance(A, (VConcatenate, HConcatenate)):
                args = [self.func(arg, B) for arg in A.args]
                if deep:
                    args = [arg.expand(deep=True) for arg in args]
                return A.func(*args)

            k = self.generate_free_symbol(free_symbol=free_symbol, integer=True)
            if len(A.shape) < 2:
                n = A.shape[0]
                
                if isinstance(A, Ref):
                    A_limit = A.limits[0]
                elif hasattr(A, "definition") and A.definition is not None:
                    A_limit = A.definition.limits[0]
                else:                    
                    A_limit = None

                if A_limit and len(B.shape) > 1:
                    j, *_ = A_limit    
                    return Ref(Sum(A[k] * B[k, j], (k, 0, n - 1)), A_limit)
                return Sum(A[k] * B[k], (k, 0, n - 1)).simplifier()                
            else:
                if isinstance(A, Ref):
                    i_limit = A.limits[0]
                else:
                    i_limit = A.definition.limits[0]

                n = A.shape[1]

                i, *_ = i_limit

                if isinstance(B, Ref):
                    j_limit = B.limits[1]
                else:
                    j_limit = B.definition.limits[1]

                j, *_ = j_limit

                return Ref(Sum(A[i, k] * B[k, j], (k, 0, n - 1)), i_limit, j_limit)

        return MatrixExpr.expand(self)


def validate(*matrices):
    """ Checks for valid shapes for args of MatMul """
    for i in range(len(matrices) - 1):
        A, B = matrices[i:i + 2]
        if A.cols != B.rows:
            raise ShapeError("Matrices %s and %s are not aligned" % (A, B))

# Rules


def newmul(*args):
    if args[0] == 1:
        args = args[1:]
    return new(MatMul, *args)


def any_zeros(mul):
    if any([arg.is_zero or (arg.is_Matrix and arg.is_ZeroMatrix)
                       for arg in mul.args]):
        matrices = [arg for arg in mul.args if arg.is_Matrix]
        return ZeroMatrix(matrices[0].rows, matrices[-1].cols)
    return mul


def merge_explicit(matmul):
    """ Merge explicit MatrixBase arguments

    >>> from sympy import MatrixSymbol, eye, Matrix, MatMul, pprint
    >>> from sympy.matrices.expressions.matmul import merge_explicit
    >>> A = MatrixSymbol('A', 2, 2)
    >>> B = Matrix([[1, 1], [1, 1]])
    >>> C = Matrix([[1, 2], [3, 4]])
    >>> X = MatMul(A, B, C)
    >>> pprint(X)
      [1  1] [1  2]
    A*[    ]*[    ]
      [1  1] [3  4]
    >>> pprint(merge_explicit(X))
      [4  6]
    A*[    ]
      [4  6]

    >>> X = MatMul(B, A, C)
    >>> pprint(X)
    [1  1]   [1  2]
    [    ]*A*[    ]
    [1  1]   [3  4]
    >>> pprint(merge_explicit(X))
    [1  1]   [1  2]
    [    ]*A*[    ]
    [1  1]   [3  4]
    """
    if not any(isinstance(arg, MatrixBase) for arg in matmul.args):
        return matmul
    newargs = []
    last = matmul.args[0]
    for arg in matmul.args[1:]:
        if isinstance(arg, (MatrixBase, Number)) and isinstance(last, (MatrixBase, Number)):
            last = last * arg
        else:
            newargs.append(last)
            last = arg
    newargs.append(last)

    return MatMul(*newargs)


def xxinv(mul):
    """ Y * X * X.I -> Y """
    from sympy.matrices.expressions.inverse import Inverse
    factor, matrices = mul.as_coeff_matrices()
    for i, (X, Y) in enumerate(zip(matrices[:-1], matrices[1:])):
        try:
            if X.is_square and Y.is_square:
                _X, x_exp = X, 1
                _Y, y_exp = Y, 1
                if isinstance(X, MatPow) and not isinstance(X, Inverse):
                    _X, x_exp = X.args
                if isinstance(Y, MatPow) and not isinstance(Y, Inverse):
                    _Y, y_exp = Y.args
                if _X == _Y.inverse():
                    if x_exp - y_exp > 0:
                        I = _X ** (x_exp - y_exp)
                    else:
                        I = _Y ** (y_exp - x_exp)
                    return newmul(factor, *(matrices[:i] + [I] + matrices[i + 2:]))
        except ValueError:  # Y might not be invertible
            pass
    return mul


def remove_ids(mul):
    """ Remove Identities from a MatMul

    This is a modified version of sympy.strategies.rm_id.
    This is necesssary because MatMul may contain both MatrixExprs and Exprs
    as args.

    See Also
    ========

    sympy.strategies.rm_id
    """
    # Separate Exprs from MatrixExprs in args
    factor, mmul = mul.as_coeff_mmul()
    # Apply standard rm_id for MatMuls
    result = rm_id(lambda x: x.is_Identity is True)(mmul)
    if result != mmul:
        return newmul(factor, *result.args)  # Recombine and return
    else:
        return mul


def factor_in_front(mul):
    factor, matrices = mul.as_coeff_matrices()
    if factor != 1:
        return newmul(factor, *matrices)
    return mul


def combine_powers(mul):
    # combine consecutive powers with the same base into one
    # e.g. A*A**2 -> A**3
    factor, mmul = mul.as_coeff_mmul()
    args = []
    base = None
    exp = 0
    for arg in mmul.args:
        if isinstance(arg, MatPow):
            current_base = arg.args[0]
            current_exp = arg.args[1]
        else:
            current_base = arg
            current_exp = 1
        if current_base == base:
            exp += current_exp
        else:
            if not base is None:
                if exp == 1:
                    args.append(base)
                else:
                    args.append(MatPow(base, exp))
#                     args.append(base ** exp)
            exp = current_exp
            base = current_base
    if exp == 1:
        args.append(base)
    else:
        args.append(MatPow(base, exp))
#         args.append(base ** exp)

    return newmul(factor, *args)


rules = (any_zeros, remove_ids, xxinv, unpack, rm_id(lambda x: x == 1),
         merge_explicit, factor_in_front, flatten, combine_powers)
canonicalize = exhaust(typed({MatMul: do_one(*rules)}))


def only_squares(*matrices):
    """factor matrices only if they are square"""
    if matrices[0].rows != matrices[-1].cols:
        raise RuntimeError("Invalid matrices being multiplied")
    out = []
    start = 0
    for i, M in enumerate(matrices):
        if M.cols == matrices[start].rows:
            out.append(MatMul(*matrices[start:i + 1]).doit())
            start = i + 1
    return out


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_MatMul(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine
    >>> X = MatrixSymbol('X', 2, 2)
    >>> expr = X * X.T
    >>> print(expr)
    X*X.T
    >>> with assuming(Q.orthogonal(X)):
    ...     print(refine(expr))
    I
    """
    newargs = []
    exprargs = []

    for args in expr.args:
        if args.is_Matrix:
            exprargs.append(args)
        else:
            newargs.append(args)

    last = exprargs[0]
    for arg in exprargs[1:]:
        if arg == last.T and ask(Q.orthogonal(arg), assumptions):
            last = Identity(arg.shape[0])
        elif arg == last.conjugate() and ask(Q.unitary(arg), assumptions):
            last = Identity(arg.shape[0])
        else:
            newargs.append(last)
            last = arg
    newargs.append(last)

    return MatMul(*newargs)


handlers_dict['MatMul'] = refine_MatMul
