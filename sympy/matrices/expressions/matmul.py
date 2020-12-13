from sympy import Number
from sympy.core import Mul, Basic, sympify
from sympy.core.compatibility import range
from sympy.functions import adjoint
from sympy.strategies import (rm_id, unpack, typed, flatten, exhaust,
        do_one, new)
from sympy.matrices.expressions.matexpr import (MatrixExpr, ShapeError,
        Identity, ZeroMatrix, GenericIdentity, Concatenate)
from sympy.matrices.expressions.matpow import MatPow
from sympy.matrices.matrices import MatrixBase
from sympy.core.logic import fuzzy_and


class MatMul(MatrixExpr):
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
        args = list(map(sympify, args))
        
        if any(arg.is_MatMul for arg in args):

            def generator():
                for arg in args:
                    if arg.is_MatMul:
                        yield from arg.args
                    else:
                        yield arg
                        
            args = [*generator()]
            
        coeffs = []        
        matrices = []

        def append(mat):            
            if matrices:
                last = matrices[-1]
                if last.is_MatPow:
                    if mat.is_MatPow:
                        if last.base == mat.base:
                            matrices[-1] = last.func(last.base, last.exp + mat.exp)
                            return
                    elif last.base == mat:                    
                        matrices[-1] = last.func(last.base, last.exp + 1)
                        return
                elif last == mat:
                    if mat._eval_inverse() == last:
                        matrices.pop()
                    else:
                        matrices[-1] = MatPow(last, 2)
                    return
            
            matrices.append(mat)
                
        for arg in args:
            if not arg.is_Mul:
                append(arg)
                continue
            
            coeff = []
            matrix = []
            for t in arg.args:
                if t.shape:
                    matrix.append(t)                        
                else:
                    coeff.append(t)
            if coeff:
                coeffs.append(Mul(*coeff))
                append(Mul(*matrix))
            else:
                append(arg)
                
        if not matrices:
            return Identity(args[0].shape[-1])
        matrices = [*filter(lambda X: not X.is_Identity, matrices)]
                        
        if len(matrices) == 1:
            mat = matrices.pop()
        else:
            
            mat = Basic.__new__(cls, *matrices)
            factor, matrices = mat.as_coeff_matrices()
            if check:
                validate(*matrices)
            if not matrices:
                # Should it be
                #
                # return Basic.__neq__(cls, factor, GenericIdentity()) ?
                mat = factor            
        
        if coeffs: 
            mat = Mul(*coeffs) * mat
                        
        return mat

    def argmax_shape(self):
        import numpy as np
        return np.argmax([len(arg.shape) for arg in self.args])

    @staticmethod
    def matmul_shape(lhs_shape, rhs_shape):
        len_lhs_shape = len(lhs_shape)
        len_rhs_shape = len(rhs_shape)
        
        if len_lhs_shape > len_rhs_shape:
            *batch_size, n, k = lhs_shape
            * _batch_size, _k = rhs_shape
            assert k == _k            
            if len(batch_size) == len(_batch_size):
                assert batch_size == _batch_size
            else:
                assert batch_size[:-len(_batch_size)] == _batch_size
            return (*batch_size, n)                
        elif len_lhs_shape < len_rhs_shape:
            *_batch_size, k = lhs_shape
            * batch_size, _k, n = rhs_shape
            assert k == _k   
            if len(batch_size) == len(_batch_size):
                assert batch_size == _batch_size
            else:
                assert batch_size[:-len(_batch_size)] == _batch_size
            return (*batch_size, n)                
        else:
            if len_lhs_shape == 1:
                assert lhs_shape == rhs_shape
                return ()
            * batch_size, n, k = lhs_shape 
            * _batch_size, _k, m = rhs_shape
            assert k == _k            
            assert batch_size == _batch_size
            return (*batch_size, n, m)
            
    @property
    def shape(self):
        shape = self.args[0].shape
        for i in range(1, len(self.args)):
            shape = self.matmul_shape(shape, self.args[i].shape)
        return shape

    def _entry(self, i, j=None, expand=True, **kwargs):
        if j is None:
            if len(self.args[0].shape) == 1:
                return self.args[0] @ self.func(*self.args[1:])[:, i]
            rhs = self.func(*self.args[1:])
            if len(rhs.shape) == 3:
                rhs = rhs[i]
            return self.args[0][i] @ rhs            
        if isinstance(i, slice):
            start, stop = i.start, i.stop
            if start is None:
                if stop is None:
                    return self.func(*self.args[:-1]) @ self.args[-1][:, j]
                start = 0
            if stop is None:
                stop = self.shape[0]
                
            return
        if expand:    
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
        else:
            return self._entry(i)[:, j]

    def as_coeff_matrices(self):
#         scalars = [x for x in self.args if not x.is_Matrix]
#         matrices = [x for x in self.args if x.is_Matrix]
        scalars = [x for x in self.args if not x.shape]
        matrices = [x for x in self.args if x.shape]

        coeff = Mul(*scalars)
#         if coeff.is_commutative == False:
#             raise NotImplementedError("noncommutative scalars in MatMul are not supported.")

        return coeff, matrices

    def as_coeff_mmul(self):
        coeff, matrices = self.as_coeff_matrices()
        return coeff, MatMul(*matrices)

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
#         from sympy.matrices.expressions.determinant import Det
        from sympy import det
        factor, matrices = self.as_coeff_matrices()
        square_matrices = only_squares(*matrices)
        return factor ** self.rows * Mul(*list(map(det, square_matrices)))

    def _eval_inverse(self):
        try:
            return MatMul(*[arg.inverse() for arg in self.args[::-1]]).doit()
        except ShapeError:
            from sympy.matrices.expressions.inverse import Inverse
            return Inverse(self)

    def doit(self, **kwargs):
        deep = kwargs.get('deep', False)
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

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a MatMul object!
        """
        if rhs.is_MatMul:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                hit = False
                for arg in intersect:
                    if arg.is_invertible:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                        hit = True
                if hit:
                    return self.func(cls(*lhs_args), cls(*rhs_args), equivalent=self).simplify()

    def simplify(self, **_):
        this = any_zeros(self)
        if this != self:
            return this
        
        from sympy import exp
        if len(self.args) == 2 and all(isinstance(arg, exp) for arg in self.args):
            if len(self.args[0].shape) < len(self.args[1].shape):
                from sympy.concrete import summations
                return summations.Sum(exp(self.args[0].arg + self.args[1].arg.T))
            
        this = self.simplifyProduct()
        if this is not self:
            return this
            
        return self

    def simplifyProduct(self):
        from sympy.concrete.products import MatProduct        
        
        for i, prod in enumerate(self.args):
            if isinstance(prod, MatProduct):
                before = self.func(*self.args[:i])
                after = self.func(*self.args[i + 1:])
                
                _prod = prod.try_absorb_forward(before)
                if _prod:
                    return _prod @ after                
                
                _prod = prod.try_absorb_backward(after)
                if _prod:
                    return before @ _prod

        return self
                
    def expand(self, free_symbol=None, deep=True, **_):
        if not deep:
            return MatrixExpr.expand(self) 
        from sympy.concrete.expr_with_limits import LAMBDA
        from sympy.concrete.summations import Sum
        if len(self.args) > 2:
            return MatrixExpr.expand(self)
        
        A, B = self.args
        if A.is_MatPow:
            return self
        if A.is_Concatenate:
            if B.is_Concatenate and len(A.shape) == 1:
                if len(A.args) == len(B.args):
                    sgm = None
                    for a, b in zip(A.args, B.args):
                        if a.shape:
                            product = a @ b
                            if product.is_MatMul and len(product.args) == 2:
                                product = product.expand()
                        else:
                            product = a * b
                        if sgm is None:
                            sgm = product
                        else:
                            sgm += product
                    return sgm
                else:
                    return self
            else:                    
                args = [self.func(arg, B).simplify() for arg in A.args]
                if deep:
                    args = [arg.expand(deep=True) if arg.is_MatMul else arg for arg in args]
                return A.func(*args)
        
        if A.is_Transpose:
            if B.is_Transpose:
                return (B.arg @ A.arg).expand().T
            if A.arg.is_Concatenate and B.is_Concatenate:
                A_T = A.arg
                if len(A_T.args) == len(B.args):
                    B_T = B._eval_transpose()
                    if B_T is not None:
                        # A @ B = A.T.T @ B.T.T = (B.T @ A.T).T
                        return (B_T @ A_T).expand().T
                        
                    sgm = None
                    for a, b in zip(A_T.args, B.args):
                        if len(a.shape) == 1 and len(b.shape) == 1:
                            n = a.shape[0]
                            if b.shape[0] == n:
                                i = a.generate_free_symbol(b.free_symbols, integer=True)
                                j = a.generate_free_symbol(b.free_symbols | {i}, integer=True)                                
                                product = LAMBDA[j:n, i:n](a[i] * b[j]).simplify()
                            else:
                                return self
                        else:
                            if not b.shape:
                                product = a * b
                            elif a.rows == b.shape[0]:
                                product = (a.T @ b).simplify()
                                if product.is_MatMul and len(product.args) == 2:
                                    X = product.args[1]
                                    if X.is_Transpose and X.arg.is_Concatenate:
                                        product = product.expand()
                            else:
                                return self
                        if sgm is None:
                            sgm = product
                        else:
                            sgm += product
                    return sgm
            return self
            
        if B.is_Concatenate:
            return self     
             
        if B.is_Transpose and B.arg.is_Concatenate:
            return (B.arg @ A.T).expand().T
              
        if A.is_MatProduct:
            return self
        
        kwargs = {'free_symbol' : free_symbol, 'generator' : self}
        
        def generate_k_limit(A, B, excludes=None, **kwargs):
            if A.is_LAMBDA or not B.is_LAMBDA:
                if excludes:
                    excludes |= B.free_symbols
                else:
                    excludes = B.free_symbols
                    
                return A.generate_int_limit(0, excludes, **kwargs)
            
            if excludes:
                excludes |= A.free_symbols
            else:
                excludes = A.free_symbols
            
            return B.generate_int_limit(0 if len(B.shape) == 1 else 1, excludes, **kwargs)

        if len(A.shape) > 1:
            i_limit = A.generate_int_limit(1, **kwargs)
            i, *_ = i_limit
            if len(B.shape) > 1:
                j_limit = B.generate_int_limit(0, {i}, **kwargs)
                j, *_ = j_limit
                
                k_limit = generate_k_limit(A, B, {i, j}, **kwargs)
                k, *_ = k_limit
                
                assert i != k and k != j and i != j
                return LAMBDA(Sum(A[i, k] * B[k, j], k_limit).simplify(), j_limit, i_limit).simplify()
            else:
                k_limit = generate_k_limit(A, B, {i}, **kwargs)
                k, *_ = k_limit
                
                assert i != k                            
                return LAMBDA(Sum(A[i, k] * B[k], k_limit).simplify(), i_limit).simplify()
        else:
#             print('A.shape =', A.shape)
            if len(B.shape) > 1:
                if B.shape[-1].is_Integer:
                    k_limit = generate_k_limit(A, B, **kwargs)
                    k, *_ = k_limit
  
                    args = []
                    for j in range(B.shape[-1]):
                        args.append(Sum(A[k] * B[k, j], k_limit).simplify())
                    return Concatenate(*args)
                else:   
#                     print('B.shape =', B.shape)                 
                    j_limit = B.generate_int_limit(0, **kwargs)
                    j, *_ = j_limit
                    
                    k_limit = generate_k_limit(A, B, {j}, **kwargs)
                    k, *_ = k_limit
                    
                    assert k != j
                    return LAMBDA(Sum(A[k] * B[k, j], k_limit).simplify(), j_limit).simplify()
            k_limit = generate_k_limit(A, B, **kwargs)
            k, *_ = k_limit
            return Sum(A[k] * B[k], k_limit).simplify()                

    def _eval_is_integer(self):
        for elem in self.args:
            is_integer = elem.is_integer
            if is_integer:
                continue
            return is_integer
        return True

    @property
    def domain(self):
        from sympy import Interval, oo
        from sympy.sets.sets import CartesianSpace
        shape = self.shape
        interval = Interval(-oo, oo, integer=self.is_integer)
        if shape:            
            return CartesianSpace(interval, *shape)
        return interval

    def _sympystr(self, p):
        from sympy.core.mul import _keep_coeff
        from sympy.printing.precedence import precedence
        c, m = self.as_coeff_mmul()
        if c.is_number and c < 0:
            expr = _keep_coeff(-c, m)
            sign = "-"
            level = precedence(expr)
        else:
            sign = ""
            level = precedence(self)

        return sign + ' @ '.join(p.parenthesize(arg, level) for arg in self.args)

    def _latex(self, p):
        from sympy import MatMul

        from sympy.printing.precedence import precedence_traditional
        parens = lambda x: p.parenthesize(x, precedence_traditional(self), False)

        args = self.args
        args = list(args)

        if isinstance(self, MatMul) and self._coeff_isneg():
            if args[0] == -1:
                args = args[1:]
            else:
                args[0] = -args[0]
            return '- ' + r' \times '.join(map(parens, args))
        else:
            return r' \times '.join(map(parens, args))

    def as_ordered_factors(self, **_):
        return [self]

    def _eval_is_extended_real(self):
        return fuzzy_and(arg.is_extended_real for arg in self.args)

    def _eval_is_extended_positive(self):
        return fuzzy_and(arg.is_extended_positive for arg in self.args)

    def _eval_is_extended_negative(self):
        return fuzzy_and(arg.is_extended_negative for arg in self.args)

    def _eval_is_finite(self):
        return fuzzy_and(arg.is_finite for arg in self.args)

    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__
    
    @property
    def dtype(self):
        dtype = None
        for arg in self.args:
            _dtype = arg.dtype
            if dtype is None or dtype in _dtype:
                dtype = _dtype
        return dtype
    
    def _eval_domain_defined(self, x):
        if x.dtype.is_set:
            return x.universalSet
        
        domain = x.domain
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain
    
    def domain_definition(self):
        eq = MatrixExpr.domain_definition(self)
        for arg in self.args:
            eq &= arg.domain_definition()        
        return eq

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

        return self.func(*(arg.T for arg in self.args[::-1]))

    def _subs(self, old, new, **hints):
        if old.is_MatMul:
            args = old.args
            for i in range(len(self.args) - len(args) + 1): 
                if all(self.args[j] == args[j - i]for j in range(i, i + len(args))):
                    return self.func(*self.args[:i] + (new.args if new.is_MatMul else (new,)) + self.args[i + len(args):]).simplify()
        return MatrixExpr._subs(self, old, new, **hints)

    @classmethod
    def rewrite_from_Sum(cls, self):
        first, second = self.function.as_two_terms() 
        from sympy.concrete.expr_with_limits import LAMBDA
        return LAMBDA(first, *self.limits) @ LAMBDA(second, *self.limits)


    
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
    if any([arg.is_zero or (arg.is_Matrix and arg.is_ZeroMatrix) for arg in mul.args]):
#         matrices = [arg for arg in mul.args if arg.is_Matrix]
        matrices = mul.args
        if len(matrices[0].shape) == 1:
            if len(matrices[-1].shape) == 1:
                from sympy import S
                return S.Zero
            return ZeroMatrix(matrices[-1].cols)
        if len(matrices[-1].shape) == 1:
            return ZeroMatrix(matrices[0].rows)
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
    factor, matrices = mul.as_coeff_matrices()
    for i, (X, Y) in enumerate(zip(matrices[:-1], matrices[1:])):
        try:
            if X.is_square and Y.is_square:
                _X, x_exp = X, 1
                _Y, y_exp = Y, 1
                if X.is_MatPow and not X.is_Inverse:
                    _X, x_exp = X.args
                if Y.is_MatPow and not Y.is_Inverse:
                    _Y, y_exp = Y.args
                if _X == _Y.inverse():
                    if x_exp - y_exp > 0:
                        I = _X ^ (x_exp - y_exp)
                    else:
                        I = _Y ^ (y_exp - x_exp)
                    return newmul(factor, *(matrices[:i] + [I] + matrices[i + 2:]))
        except (ValueError, AttributeError):  # Y might not be invertible
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
    for arg in mmul.args if mmul.is_MatMul else (mmul,):
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
    if matrices[0].shape[-2] != matrices[-1].shape[-1]:
        raise RuntimeError("Invalid matrices being multiplied")
    out = []
    start = 0
    for i, M in enumerate(matrices):
        if M.shape[-1] == matrices[start].shape[-2]:
            args = matrices[start:i + 1]
            if len(args) == 1:
                mat = args[0]
            else:
                mat = MatMul(*args).doit()
            out.append(mat)
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
