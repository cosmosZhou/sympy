from sympy.core import Basic
from sympy.functions import conjugate
from sympy.matrices.expressions.transpose import transpose
from sympy.matrices.expressions.matexpr import MatrixExpr
from sympy.core.cache import cacheit


class Adjoint(MatrixExpr):
    """
    The Hermitian adjoint of a matrix expression.

    This is a symbolic object that simply stores its argument without
    evaluating it. To actually compute the adjoint, use the ``adjoint()``
    function.

    Examples
    ========

    >>> from sympy.matrices import MatrixSymbol, Adjoint
    >>> from sympy.functions import adjoint
    >>> A = MatrixSymbol('A', 3, 5)
    >>> B = MatrixSymbol('B', 5, 3)
    >>> Adjoint(A*B)
    Adjoint(A*B)
    >>> adjoint(A*B)
    Adjoint(B)*Adjoint(A)
    >>> adjoint(A*B) == Adjoint(A*B)
    False
    >>> adjoint(A*B) == Adjoint(A*B).doit()
    True
    """
    def __new__(cls, arg, **kwargs):
        if kwargs.get('evaluate', True):
            if (ret := arg._eval_adjoint()) is not None:
                return ret

        return MatrixExpr.__new__(cls, arg)
    
    @property
    def dtype(self):
        return self.arg.dtype
    
    def doit(self, **hints):
        arg = self.arg
        if hints.get('deep', True) and isinstance(arg, Basic):
            arg = arg.doit(**hints)
            if arg != self.arg:
                return self.func(arg)
        
        return self

    @property
    def arg(self):
        return self.args[0]

    @cacheit
    def _eval_shape(self):
        shape = self.arg.shape 
        if len(shape) > 1:
            [*shape] = shape
            axis = -1
            shape[-1], shape[-2] = shape[-2], shape[-1]
            return tuple(shape)
        return shape

    def _entry(self, i, j, **kwargs):
        return conjugate(self.arg[j, i])

    def _eval_adjoint(self):
        return self.arg

    def _eval_conjugate(self):
        return transpose(self.arg)

    def _eval_trace(self):
        from sympy.matrices.expressions.trace import Trace
        return conjugate(Trace(self.arg))

    def _eval_transpose(self, axis=-1):
        if axis == self.default_axis:
            return conjugate(self.arg)

    def _latex(self, p, exp=None):
        arg = p._print(self.arg)
        tex = r'%s^{\color{magenta} {\dagger}}' % arg
        if exp:
            tex = r'\left(%s\right)^{%s}' % (tex, p._print(exp))
        return tex
