from sympy.core.function import Function
from sympy.concrete.summations import Sum

class Reduced(Function):
    ...
    
class ReducedSum(Reduced):
    r"""Represents unevaluated reduced summation.
    input must be a multi-dimensional tensor
    """
    is_complex = True
    
    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False

    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm             
            return self.func(rest).doit(deep=deep) + sgm
        else:
            return self
        return f

    @property
    def shape(self):
        return self.arg.shape[:-1]

    @property
    def dtype(self):
        return self.arg.dtype

    def _sympystr(self, p):
        return '\N{N-ARY SUMMATION}(%s)' % p._print(self.arg)

    def _latex(self, p, exp=None):
        expr = p._print(self.arg)
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr
        expr = r"\sum{%s}" % expr
        if exp is None:
            return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log
        from sympy.concrete.products import Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Lamda:
            if len(self.arg.limits) == 1 and not self.arg.variable.shape:
                function = self.arg.expr
                self = Sum(function, *self.arg.limits).simplify(**kwargs)
        elif self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self

class ReducedMin(Function):
    r"""Represents unevaluated reduced minimize.
    input must be a multi-dimensional tensor
    """
    is_extended_real = True
    
    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False

    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm             
            return self.func(rest).doit(deep=deep) + sgm
        else:
            return self
        return f

    @property
    def shape(self):
        return self.arg.shape[:-1]

    @property
    def dtype(self):
        return self.arg.dtype

    def _sympystr(self, p):
        return 'min(%s)' % p._print(self.arg)

    def _latex(self, p, exp=None):
        expr = p._print(self.arg)
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr
        expr = r"\min{%s}" % expr
        if exp is None:
            return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log
        from sympy.concrete.products import Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Lamda:
            if len(self.arg.limits) == 1 and not self.arg.variable.shape:
                function = self.arg.expr
                from sympy import Minima
                self = Minima(function, *self.arg.limits).simplify(**kwargs)
        elif self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self


class ReducedMax(Function):
    r"""Represents unevaluated reduced maximize.
    input must be a multi-dimensional tensor
    """
    is_extended_real = True
    
    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.arg.is_zero:
            return True
        
        if self.arg.is_extended_positive or self.arg.is_extended_negative:
            return False

    def doit(self, **hints):
        deep = hints.get('deep', True)
        if deep:
            f = self.arg.doit(**hints)
        else:
            f = self.arg

        if f.is_FiniteSet:
            x, *args = f.args
            rest = f.func(*args)
            from sympy import NotElement, Bool
            sgm = x * Bool(NotElement(x, rest).simplify()).simplify()
            if not rest:
                return sgm             
            return self.func(rest).doit(deep=deep) + sgm
        else:
            return self
        return f

    @property
    def shape(self):
        return self.arg.shape[:-1]

    @property
    def dtype(self):
        return self.arg.dtype

    def _sympystr(self, p):
        return 'min(%s)' % p._print(self.arg)

    def _latex(self, p, exp=None):
        expr = p._print(self.arg)
        if self.arg.is_Add or self.arg.is_MatMul:
            expr = r"\left(%s\right)" % expr
        expr = r"\max{%s}" % expr
        if exp is None:
            return expr
        return r"\left(%s\right)^{%s}" % (expr, exp)
    
    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_extended_real(self):
        return self.arg.is_extended_real

    def _eval_is_extended_positive(self):
        return self.arg.is_extended_positive
    
    def _eval_is_extended_negative(self):
        return self.arg.is_extended_negative

    def _eval_exp(self):
        from sympy import log
        from sympy.concrete.products import Product
        if isinstance(self.arg, log):
            return Product(self.arg.arg, *self.limits)

    def _eval_derivative(self, x):
        from sympy.core.function import Derivative
        return Derivative(self.astype(Sum), x, evaluate=True).simplify()
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        if self.arg.is_Lamda:
            if len(self.arg.limits) == 1 and not self.arg.variable.shape:
                function = self.arg.expr
                from sympy import Maxima
                self = Maxima(function, *self.arg.limits).simplify(**kwargs)
        elif self.arg.is_Piecewise:
            self = self.arg.func(*((self.func(e).simplify(), c) for e, c in self.arg.args)).simplify()
        elif self.arg.is_Mul:
            args = []
            coeff = []
            for arg in self.arg.args:
                if arg.shape:
                    args.append(arg)
                else:
                    coeff.append(arg)
                                
            if coeff:
                coeff = self.arg.func(*coeff)
                function = self.arg.func(*args)
                return coeff * self.func(function)
        return self


class ReducedArgMinMaxBase(Function):
    r"""Represents unevaluated reduced ArgMax.
    input must be a multi-dimensional tensor
    """
    
    is_integer = True
    
    @property
    def shape(self):
        return self.arg.shape[:-1]

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.integer

    def _sympystr(self, p):
        return '%s(%s)' % (self.__class__.__name__, p._print(self.arg))

    def _latex(self, p, exp=None):
        name = self.__class__.__name__.lower()[-3:]
        tex = r'\mathop{{\rm %s}^{-1}}' % name
        
        if self.arg.is_Add:
            tex += r"\left(%s\right)" % p._print(self.arg)
        else:
            tex += p._print(self.arg)

        return tex
    
    def _eval_is_finite(self):
        return True

    def _eval_is_extended_real(self):
        return True

    def _eval_is_extended_positive(self):
        ...
    
    def _eval_is_extended_negative(self):
        ...

    def _eval_is_extended_nonnegative(self):
        return True
        
    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices):
        return self.func(self.arg[indices])
        
    def simplify(self, deep=False, **kwargs):
        return self


class ReducedArgMax(ReducedArgMinMaxBase):
    r"""Represents unevaluated reduced ArgMax.
    input must be a multi-dimensional tensor
    """
    
class ReducedArgMin(ReducedArgMinMaxBase):
    r"""Represents unevaluated reduced ArgMin.
    input must be a multi-dimensional tensor
    """
    