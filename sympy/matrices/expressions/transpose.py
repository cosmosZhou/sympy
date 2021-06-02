from sympy import Basic
from sympy.functions import adjoint, conjugate

from sympy.matrices.expressions.matexpr import MatrixExpr
from sympy.core.sympify import _sympify


class Transpose(MatrixExpr):
    """
    The transpose of a matrix expression.

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the transpose, use the ``transpose()``
    function, or the ``.T`` attribute of matrices.

    Examples
    ========

    >>> from sympy.matrices import MatrixSymbol, Transpose
    >>> from sympy.functions import transpose
    >>> A = MatrixSymbol('A', 3, 5)
    >>> B = MatrixSymbol('B', 5, 3)
    >>> Transpose(A)
    A.T
    >>> A.T == transpose(A) == Transpose(A)
    True
    >>> Transpose(A*B)
    (A*B).T
    >>> transpose(A*B)
    B.T*A.T

    """

    @property
    def dtype(self):
        return self.arg.dtype

    def __new__(cls, arg, **kwargs):        
        arg = _sympify(arg)
        
        if kwargs.get('evaluate', True):
            transpose = arg._eval_transpose()
            if transpose is not None:
                return transpose
            
        return MatrixExpr.__new__(cls, arg, **kwargs)
    
    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
        return "%s.T" % p.parenthesize(self.arg, PRECEDENCE["Pow"])

    def _latex(self, p): 
        if self.arg.is_BlockMatrix:
            X = self.arg
            return r"{\left(\begin{array}{%s}%s\end{array}\right)}" % ('c' * len(X.args),
                                                                        ' & '.join('{%s}' % p._print(arg.T) for arg in X.args))

        else:
            from sympy.printing.precedence import precedence_traditional
            return r"{%s}^{\color{magenta} T}" % p.parenthesize(self.arg, precedence_traditional(self), True)

    def doit(self, **hints):
        arg = self.arg
        if hints.get('deep', True) and isinstance(arg, Basic):
            arg = arg.doit(**hints)
        _eval_transpose = getattr(arg, '_eval_transpose', None)
        if _eval_transpose is not None:
            result = _eval_transpose()
            return result if result is not None else self
        else:
            return self

    @property
    def arg(self):
        return self.args[0]

    @property
    def shape(self):        
        shape = self.arg.shape
        assert len(shape) > 1
        return (*shape[:-2], shape[-1], shape[-2])

    def _entry(self, i, j=None, expand=False, **kwargs):
        if j is None:
            if len(self.shape) > 2:
                return self.arg[i].T
            
            if isinstance(i, slice):
                start, stop = i.start, i.stop
                if start is None:
                    if stop is None:
                        return self
                from sympy import Slice                
                return Slice(self.arg, slice(None, None), i)
            return self.arg[:, i]            
        if hasattr(self.arg, '_entry'):
            return self.arg._entry(j, i, expand=expand, **kwargs)
        else:
            return self.arg[j, i]

    def _eval_adjoint(self):
        return conjugate(self.arg)

    def _eval_conjugate(self):
        return adjoint(self.arg)

    def _eval_transpose(self):
        return self.arg

    def _eval_trace(self):
        from .trace import Trace
        return Trace(self.arg)  # Trace(X.T) => Trace(X)

    def _eval_determinant(self):
        from sympy.matrices.expressions.determinant import det
        return det(self.arg)

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real
    
    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative
    
    def _eval_is_finite(self):
        return self.arg.is_finite    

    def _eval_derivative_matrix_lines(self, x):
        lines = self.args[0]._eval_derivative_matrix_lines(x)
        return [i.transpose() for i in lines]

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Transpose object!
        """
        if rhs.is_Transpose:
            return self.func(lhs.arg, rhs.arg)

    def simplify(self, **_):
        from sympy.core.function import Function
        from sympy.core.mul import Mul
        f = self.arg
        if isinstance(f, Function):
            return f.func(self.func(f.arg).simplify())
        if isinstance(f, Mul):
            if len(f.args[0].shape) == 0:
                return f.func(f.args[0], self.func(f.func(*f.args[1:])).simplify())

        return self

    def _eval_domain_defined(self, x):
        domain = MatrixExpr._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def __getitem__(self, key):
        if not isinstance(key, tuple) and isinstance(key, slice):
            return self._entry(key)
        if isinstance(key, tuple): 
            if len(key) == 1:
                key = key[0]
            elif len(key) == 2:
                i, j = key
                if isinstance(i, slice):
                    if isinstance(j, slice):
                        return self._entry(i, j)
                    else:
                        return self.func(self.arg[j])
#                     return MatrixSlice(self, i, j)
                i, j = _sympify(i), _sympify(j)
                if self.valid_index(i, j) != False:
                    return self._entry(i, j)
                else:
                    raise IndexError("Invalid indices (%s, %s)" % (i, j))
        from sympy import Integer, Symbol, Expr
        if isinstance(key, (int, Integer, Symbol, Expr)):
            return self._entry(key)
#             # row-wise decomposition of matrix
        raise IndexError("Invalid index, wanted %s[i,j]" % self)


def transpose(expr):
    """Matrix transpose"""
    return Transpose(expr).doit(deep=False)


from sympy.assumptions.ask import ask, Q
from sympy.assumptions.refine import handlers_dict


def refine_Transpose(expr, assumptions):
    """
    >>> from sympy import MatrixSymbol, Q, assuming, refine
    >>> X = MatrixSymbol('X', 2, 2)
    >>> X.T
    X.T
    >>> with assuming(Q.symmetric(X)):
    ...     print(refine(X.T))
    X
    """
    if ask(Q.symmetric(expr), assumptions):
        return expr.arg

    return expr


handlers_dict['Transpose'] = refine_Transpose
