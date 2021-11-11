r"""Module that defines indexed objects

The classes ``IndexedBase``, ``Indexed``, and ``Idx`` represent a
matrix element ``M[i, j]`` as in the following diagram::

       1) The Indexed class represents the entire indexed object.
                  |
               ___|___
              '       '
               M[i, j]
              /   \__\______
              |             |
              |             |
              |     2) The Idx class represents indices; each Idx can
              |        optionally contain information about its range.
              |
        3) IndexedBase represents the 'stem' of an indexed object, here `M`.
           The stem used by itself is usually taken to represent the entire
           array.

There can be any number of indices on an Indexed object.  No
transformation properties are implemented in these Base objects, but
implicit contraction of repeated indices is supported.

Note that the support for complicated (i.e. non-atomic) integer
expressions as indices is limited.  (This should be improved in
future releases.)

Examples
========

To express the above matrix element example you would write:

>>> from sympy import symbols, IndexedBase, Idx
>>> M = IndexedBase('M')
>>> i, j = symbols('i j', cls=Idx)
>>> M[i, j]
M[i, j]

Repeated indices in a product implies a summation, so to express a
matrix-vector product in terms of Indexed objects:

>>> x = IndexedBase('x')
>>> M[i, j]*x[j]
M[i, j]*x[j]

If the indexed objects will be converted to component based arrays, e.g.
with the code printers or the autowrap framework, you also need to provide
(symbolic or numerical) dimensions.  This can be done by passing an
optional shape parameter to IndexedBase upon construction:

>>> dim1, dim2 = symbols('dim1 dim2', integer=True)
>>> A = IndexedBase('A', shape=(dim1, 2*dim1, dim2))
>>> A.shape
(dim1, 2*dim1, dim2)
>>> A[i, j, 3].shape
(dim1, 2*dim1, dim2)

If an IndexedBase object has no shape information, it is assumed that the
array is as large as the ranges of its indices:

>>> n, m = symbols('n m', integer=True)
>>> i = Idx('i', m)
>>> j = Idx('j', n)
>>> M[i, j].shape
(m, n)
>>> M[i, j].ranges
[(0, m - 1), (0, n - 1)]

The above can be compared with the following:

>>> A[i, 2, j].shape
(dim1, 2*dim1, dim2)
>>> A[i, 2, j].ranges
[(0, m - 1), None, (0, n - 1)]

To analyze the structure of indexed expressions, you can use the methods
get_indices() and get_contraction_structure():

>>> from sympy.tensor import get_indices, get_contraction_structure
>>> get_indices(A[i, j, j])
({i}, {})
>>> get_contraction_structure(A[i, j, j])
{(j,): {A[i, j, j]}}

See the appropriate docstrings for a detailed explanation of the output.
"""

#   TODO:  (some ideas for improvement)
#
#   o test and guarantee numpy compatibility
#      - implement full support for broadcasting
#      - strided arrays
#
#   o more functions to analyze indexed expressions
#      - identify standard constructs, e.g matrix-vector product in a subexpression
#
#   o functions to generate component based arrays (numpy and sympy.Matrix)
#      - generate a single array directly from Indexed
#      - convert simple sub-expressions
#
#   o sophisticated indexing (possibly in subclasses to preserve simplicity)
#      - Idx with range smaller than dimension of Indexed
#      - Idx with stepsize != 1
#      - Idx with step determined by function call

from sympy.core import Expr, Tuple, Symbol, sympify, S
from sympy.core.compatibility import (is_sequence, NotIterable,
                                      Iterable)
from sympy.core.sympify import _sympify


class IndexException(Exception):
    pass


class Indexed(Expr):
    """Represents a mathematical object with indices.

    >>> from sympy import Indexed, IndexedBase, Idx, symbols
    >>> i, j = symbols('i j', cls=Idx)
    >>> Indexed('A', i, j)
    A[i, j]

    It is recommended that ``Indexed`` objects be created via ``IndexedBase``:

    >>> A = IndexedBase('A')
    >>> Indexed('A', i, j) == A[i, j]
    True

    """
    is_commutative = True
    is_symbol = True
    is_Atom = True

    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            if len(indices) >= 2 and isinstance(indices[0], slice):
                if isinstance(indices[1], slice):
                    start, stop = indices[1].start, indices[1].stop
                    if start is None and stop is None:
                        return self[indices[0]].T
                    return Slice(self, *indices)
                
                start, stop = indices[0].start, indices[0].stop
                if start is None:
                    if stop is None:
                        return self.T[indices[1]]
                    start = 0
                if stop is None:
                    stop = self.shape[0]
                return self[start:stop].T[indices[1]]
                
            indices = self.indices + tuple(indices)
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            if stop is None:
                stop = self.shape[0]
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            if start == 0 and stop == self.shape[0]:
                return self
            return Slice(self, indices, **kw_args)
        else:
            indices = self.indices + (indices,)
            
        assert len(indices) <= len(self.base.shape)
        return Indexed(self.base, *indices, **kw_args)

    def image_set(self):
        definition = self.base.definition
        if definition is None:
            return
        return definition[self.indices].image_set()

    def element_symbol(self, excludes=set()):
        etype = self.etype
        if etype is None:
            return

        return self.generate_var(excludes=excludes, **etype.dict)

# performing other in self
    def __contains__(self, other):
        if other.is_Intersection:
            if self in other._argset:
                return True
        definition = self.base.defun()
        if definition  is not None:
            try: 
                return other in definition [self.indices]
            except TypeError:
                ...
        
    def _eval_is_integer(self):
        if not hasattr(self.base, 'is_integer') and self.base.definition is not None:
            return self.base.definition.is_integer
        return self.base.is_integer

    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if isinstance(other, (Symbol, Indexed, Slice)):
            return self.shape == other.shape
        return False

    def __new__(cls, base, *args, **kw_args):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.matrices.matrices import MatrixBase

        if not args:
            return base
#             raise IndexException("Indexed needs at least one index.")
        if isinstance(base, str):
            base = Symbol(base, shape=(S.Infinity,))
        elif isinstance(base, Symbol):
            assert base.shape
        elif not hasattr(base, '__getitem__') and not base.is_Symbol:
            assert len(base.shape) >= len(args)
        args = list(map(sympify, args))
        
        if isinstance(base, (NDimArray, Tuple, MatrixBase)) and all([i.is_number for i in args]):
            if len(args) == 1:
                return base[args[0]]
            else:
                return base[args]
        if base.is_Lamda:
            return base[args]
            
        if len(args) == 1 and args[0].is_Piecewise:
            piecewise = args[0]
            return piecewise.func(*((cls(base, e), c) for e, c in piecewise.args))
            
        return Expr.__new__(cls, base, *args, **kw_args)

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True

    @property
    def is_set(self):
        return self.base.type[self.indices].is_set

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    base = property(lambda self: self.args[0])
    indices = property(lambda self: self.args[1:])
    index = property(lambda self: self.args[1])
    shape = property(lambda self: self.base.shape[len(self.indices):])
    
    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def _sympystr(self, p):
        indices = list(map(p.doprint, self.indices))
        return "%s[%s]" % (p.doprint(self.base), ", ".join(indices))

    def _latex(self, p):
        shape = self.base.shape
        tex_base = p._print(self.base)
        if self.is_random:
            tex_base = r'{\color{red} {%s}}' % tex_base
        indices = [*self.indices]
        
        for i, index in enumerate(indices):
            length = shape[i]
            if index.is_Add:
                if length in index.args:
                    negative_index = index - length
                    if negative_index.is_extended_negative:
                        indices[i] = negative_index
                 
        return '{' + tex_base + '}' + '_{%s}' % ','.join(map(p._print, indices))

    @property
    def free_symbols(self):
        base = self.base
        if 'definition' in base._assumptions:
            base_free_symbols = base.free_symbols
        else:
            base_free_symbols = base.free_symbols | {self}
            
        indices_free_symbols = {fs for i in self.indices for fs in i.free_symbols}
        if base_free_symbols:
            return base_free_symbols | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}
    
    # return exp._has(self)
    def has_match(self, exp):
        from sympy.core.symbol import Wild
        if exp.is_Indexed and exp.base == self.base:
            if len(exp.indices) == 1:
                index_fixed, *_ = self.indices
                if isinstance(index_fixed, Wild):
                    return False
                index, *_ = exp.indices

                if index < index_fixed:
                    return False
                if index > index_fixed:
                    return False
                # it is possible for them to be equal!
                return True

        if exp.is_Slice:
            if exp.base == self.base:
                if len(self.indices) == 1:
                    start, stop = exp.index
                    index_fixed, *_ = self.indices
    
                    if isinstance(index_fixed, Wild):
                        return False
    
                    if stop <= index_fixed:
                        return False
                    if start > index_fixed:
                        return False
                    # it is possible for them to be equal!
                    return True
            else:
                base = exp.base.definition
                if base is not None and base._has(self):
                    return True
            
        if isinstance(exp, Symbol) and exp == self.base:
            if len(self.indices) == 1:
                start, stop = 0, exp.shape[-1]
                index_fixed, *_ = self.indices

                if isinstance(index_fixed, Wild):
                    return False

                if stop <= index_fixed:
                    return False
                if start > index_fixed:
                    return False
                # it is possible for them to be equal!
                return True
            
        return False

    def _has(self, pattern):
        if pattern.is_Tuple:
            return any(self._has(pattern) for pattern in pattern)
        """Helper for .has()"""
        if pattern.is_Indexed:
            if pattern.base == self.base:
                if pattern.indices == self.indices:
                    return True
                
        if any(arg._has(pattern) for arg in self.indices):
            return True
        from sympy.core.assumptions import ManagedProperties
        
        if not isinstance(pattern, ManagedProperties) and hasattr(pattern, 'has_match') and pattern.has_match(self):
            return True
            
        from sympy.core.function import FunctionClass
        
        if isinstance(pattern, (FunctionClass, ManagedProperties)):
            return self.base._has(pattern)
        else: 
            if self.base.is_AppliedUndef:
                return any(arg._has(pattern) for arg in self.base.args)
                                
            definition = self.definition
            if definition is not None:
                return definition._has(pattern)
            if self.base.is_Transpose:
                if self.base.arg == pattern:
                    return True
        
        return False

    def _subs(self, old, new, **hints):
        if self.base == old:
            return new[self.indices]

        this = Expr._subs(self, old, new, **hints)
        if this != self:
            return this
        if hints.get('symbol') is not False:
            if self.base.is_AppliedUndef:
                ...
            else:
                definition = self.definition
                if definition is not None:
                    this = definition._subs(old, new, **hints)
                    if this != definition:
                        return this
        return self             

    def _subs_slice(self, old, new, **hints): 
        if self.base == old.base and len(self.indices) >= len(old.indices):
            self_indices = self.indices
            old_indices = old.indices
            
            if len(self_indices) > len(old_indices):
                old_indices = [*old_indices]  # make a copy first
                shape = self.base.shape
                while len(self_indices) > len(old_indices): 
                    old_indices.append((0, shape[len(old_indices)]))
#             elif len(self_indices) < len(old_indices):
                # could not substitute for an index with fewer args than that of a slice                                                        
                    
            indices = []
            for k, (start, stop) in zip(self_indices, old_indices):
                if k >= start and k < stop:
                    indices.append(k - start)
                else: 
                    break
            else: 
                return new[tuple(indices)]
        return Expr._subs_slice(self, old, new, **hints)

    def _eval_is_random(self):
        return self.base.is_random

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution                
                return AbstractContinuousDistribution(definition) 

    @property
    def dtype(self):
        return self.base.dtype

    def _eval_domain_defined(self, x, **_):
        from sympy import Range
        for i, index in enumerate(self.indices):
            if not x.shape and index._has(x) and not x.is_set:
                diff = x - index
                if diff.free_symbols & index.free_symbols:
                    continue
                domain = Range(diff, self.base.shape[i] + diff)
                return x.domain & domain
        if not self.base.is_AppliedUndef:
            definition = self.definition
            if definition is not None:
                return definition.domain_defined(x)
        
        if x.dtype.is_set:
            return x.universalSet
        domain = x.domain          
         
        for index in self.indices:
            domain &= index.domain_defined(x)
        return domain

    @property
    def definition(self):
        
        definition = self.base.defun()
        if definition is not None:
            try:
                return definition[self.indices]
            except:
                ...
    
    def defun(self):
        
        definition = self.base.defun()
        if definition is not None:
            try:
                return definition[self.indices]
            except:
                ...
                
    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_complex(self):
        return self.base.is_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.indices]

    def equality_defined(self):
        from sympy import Equal
        return Equal(self, self.definition, evaluate=False)

    def _eval_determinant(self):
        definition = self.definition
        if definition is not None:
            return definition._eval_determinant()

    def generate_int_limit(self, *args, **kwargs):
        definition = self.definition
        if definition is not None:
            return definition.generate_int_limit(*args, **kwargs) 
        return Expr.generate_int_limit(self, *args, **kwargs)
      
    def _eval_transpose(self):
        if len(self.shape) < 2:
            return self
        
        definition = self.definition
        if definition is not None:
            if definition.T == definition:
                return self

    @property
    def domain(self): 
        if self.is_set:
            return self.universalSet
        definition = self.defun()
        if definition is not None:
            return definition.domain
        
        from sympy import Interval, Range
        domain = self.base.domain_assumed
        if domain is None:
            
            assumptions = self.base.assumptions0
            integer = assumptions.pop('integer', None)
            if integer:
                domain = Range(**assumptions)
            else:
                domain = Interval(**assumptions)
            
        shape = self.shape
        if not shape:
            return domain
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(domain, *shape)

    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def is_given(self): 
        return self.base.is_given
#         if self.base.is_given:
#             return True
#         return all(index.is_given for index in self.indices)

    def as_boolean(self):
        if self.is_random:
            from sympy import Equal
            from sympy.stats.rv import pspace
            return Equal(self, pspace(self).symbol)

    def condition_set(self):
        definition = self.definition
        if definition is None:
            return
        return definition.condition_set()

    def doit(self, **hints):
        indices = tuple(index.doit(**hints) for index in self.indices)
        if indices == self.indices:
            return self
        return self.base[indices] 

    def is_continuous(self, *args):
        definition = self.definition
        if definition is None:
            return True
        return definition.is_continuous(*args)

class Slice(Expr):
    """Represents a mathematical object with Slices.

    """
    is_symbol = True
    is_Atom = True

    base = property(lambda self: self.args[0])
    start = property(lambda self: self.args[1][0])
    stop = property(lambda self: self.args[1][1])    
    indices = property(lambda self: self.args[1:])
    index = property(lambda self: self.args[1])

    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.start:self.stop]

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution                
                return AbstractContinuousDistribution(definition) 

    @property
    def definition(self):
        definition = self.base.definition
        if definition is not None:
            return definition[self.start:self.stop]

    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def domain(self): 
        if self.dtype.is_set:
            return self.universalSet    

        from sympy import Interval, Range
        domain = self.base.domain_assumed
        if domain is None:
            assumptions = self.base.assumptions0
            integer = assumptions.pop('integer', None)
            if integer:
                domain = Range(**assumptions)
            else:
                domain = Interval(**assumptions)
            
        shape = self.shape
        if not shape:
            return domain
        from sympy.sets.sets import CartesianSpace
        return CartesianSpace(domain, *shape)

    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if other.is_symbol:
            return self.shape == other.shape
        return False

# performing other.indices in self.indices
    def index_contains(self, other):
        if not (other.is_Indexed or other.is_Slice) or self.base != other.base: 
            return False
        
        if len(other.indices) != len(self.indices):
            return False

        if other.is_Slice:
            return all(_start >= start and _stop <= stop for (start, stop), (_start, _stop) in zip(self.indices, other.indices)) 
        else:
            return all(index >= start and index < stop for (start, stop), index in zip(self.indices, other.indices))

    def set_comprehension(self, var=None):
        from sympy.concrete.sets import Cup
        i = self.generate_var(integer=True, var=var)
        return Cup({self.base[i]}, (i, *self.index))

    def __new__(cls, base, *indices, **kw_args):
        if not indices:
            raise IndexException("Indexed needs at least one index.")

        indices = [*indices]
        for i, index in enumerate(indices):
            if isinstance(index, slice):
                start, stop = index.start, index.stop
            else:
                start, stop = index
                
            if start is None:
                start = S.Zero
            elif start < 0:
                start = base.shape[i] + start
            else:
                start = sympify(start)
                    
            if stop is None:
                stop = base.shape[i]
            elif stop < 0:
                stop = base.shape[i] + stop
            else: 
                stop = sympify(stop)
                
            assert start != stop, "%s != %s" % (start, stop)
            indices[i] = Tuple(start, stop)

        if isinstance(base, str):
            from sympy import oo
            base = Symbol(base, shape=(oo,))
        elif base.is_Symbol:
            assert base.shape
            if start.is_zero and stop == base.shape[len(indices) - 1]:
                indices = indices[:-1]
                if indices:
                    return base[indices]
                return base
            
            start, stop = indices[0]
            if stop == start + 1:
                base = base[start]
                indices = indices[1:]
                if indices:
                    return base[indices]
                return base
                    
        elif not hasattr(base, '__getitem__') and not isinstance(base, Symbol):
            assert len(base.shape) >= len(indices)            
        elif base.is_Lamda:
            start, stop = indices
            return base[start: stop]
        
        return Expr.__new__(cls, base, *indices, **kw_args)

    def __iter__(self):
        raise TypeError

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            if len(self.indices) > len(indices):
                if len(indices) == 0:
                    return self
                return
            elif len(self.indices) < len(indices):
                return
            else: 
                base = self.base
                for (start, stop), index in zip(self.indices, indices):
                    if isinstance(index, slice):
                        b, e = index.start, index.stop
                        base = base[b + start: e + start]
                    else: 
                        base = base[index + start]
                return base 
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0                
            if stop is None:
                stop = self.shape[0]
            if start == stop - 1:
                return self[start]
            self_start, self_stop = self.index
            start, stop = self_start + start, self_start + stop
#             assert stop <= self_stop, "try to prove, %s <= %s" % (stop, self_stop)
            return self.base[start: stop]
        else:
            start, stop = self.index
            return self.base[indices + start]

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @property
    def shape(self):
        sizes = [stop - start for start, stop in self.indices]
        
        if len(self.base.shape) > len(sizes):
            sizes += [self.base.shape[i] for i in range(len(sizes), len(self.base.shape))]

        return tuple(sizes)

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def index_generator(self, p):
        base_shape = self.base.shape
        for i, (start, stop) in enumerate(self.indices):
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
                
            if stop == base_shape[i]:
                stop = ''
            else:
                stop = p._print(stop)
                
            yield ':'.join([start, stop])

    def _sympystr(self, p): 
        return "%s[%s]" % (p.doprint(self.base), ', '.join(self.index_generator(p)))

    def _latex(self, p):
        if self.base.is_Indexed:
            indices = [p._print(index) for index in self.base.indices]
            indices += [*self.index_generator(p)]
            
            tex = '{%s}_{%s}' % (p._print(self.base.base), ', '.join(indices))        
        else:
            tex = '{%s}_{%s}' % (p._print(self.base), ', '.join(self.index_generator(p)))
        return tex

    @property
    def free_symbols(self):
        base_free_symbols = self.base.free_symbols
        indices_free_symbols = {fs for i in self.indices for fs in i.free_symbols}
        if base_free_symbols:
            return {self} | base_free_symbols | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    # return exp._has(self)
    def has_match(self, expr):
        if expr.is_Indexed and expr.base == self.base:
            if len(expr.indices) == 1:

                index, *_ = expr.indices
                start, stop = self.index

                if index < start:
                    return False  # index < start
                if index >= stop:
                    return False  # index >= stop
# it is possible for them to be equal!
                return True
        if expr.is_Slice:
            if expr.base == self.base:
                for _index, index in zip(expr.indices, self.indices):
                    index_start, index_stop = _index
                    start, stop = index
        
                    if index_stop <= start:
                        return False  # index < start
                    if index_start >= stop:
                        return False  # index >= stop
    # it is still possible for them to be equal!
                return True
            else:
                base = expr.base.definition
                if base is not None and base._has(self):
                    return True
        return False

    def _has_matcher(self):
        """Helper for .has()"""
        return self.match

    def _has(self, pattern):
        """Helper for .has()"""
        from sympy.core.function import UndefinedFunction, Function
        if isinstance(pattern, UndefinedFunction):
            return any(f.func == pattern or f == pattern for f in self.atoms(Function, UndefinedFunction))

        pattern = sympify(pattern)
        from sympy.core.core import BasicMeta
        from sympy import preorder_traversal
        
        if isinstance(pattern, BasicMeta):
            return any(isinstance(arg, pattern) for arg in preorder_traversal(self))

        has_match = getattr(pattern, 'has_match', None)
        if has_match is not None: 
            if has_match(self):
                return True
            args = self.args[1:]
        else:
            if self == pattern:
                return True
            args = self.args

        if any(arg._has(pattern) for arg in args):
            return True
        
        definition = self.base.definition
        if definition is not None: 
            if hasattr(definition, '__getitem__'):
                from sympy.core.symbol import Dummy
                from sympy import Range
                k = Dummy('k', integer=True, domain=Range(*self.index))
                return definition[k]._has(pattern)
            else:
                args = definition.args
                if any(arg._has(pattern) for arg in args):
                    return True                
        
        return False

    @property
    def dtype(self):
        return self.base.dtype

    def _eval_is_integer(self): 
        return self.base.is_integer

    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_complex(self):
        return self.base.is_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def _eval_is_random(self):
        return self.base.is_random
    
    @property
    def is_given(self): 
        return self.base.is_given

    def as_boolean(self):
        if self.is_random:
            from sympy import Equal
            from sympy.stats.rv import pspace
            return Equal(self, pspace(self).symbol)

    def _eval_domain_defined(self, x, allow_empty=False, **_):
        domain = self.base.domain_defined(x)
        start, stop = self.index
        if allow_empty:
            domain &= x.domain_conditioned(start <= stop)
        else:
            domain &= x.domain_conditioned(start < stop)
        return domain

    def domain_definition(self):
        base, (start, stop), *_ = self.args
        size = base.shape[-1]
        from sympy import And
        return And(start >= 0, start < stop, stop <= size)

    @property
    def T(self):
        if len(self.shape) < 2:
            return self
        return super(Slice, self).T

    def _subs(self, old, new, **kwargs):
        if self == old:
            return new
        if self.base == old:
            return new[slice(*self.index)]
            
        return Expr._subs(self, old, new, **kwargs)
    
    def _subs_slice(self, old, new, **hints):
        if self.base == old.base and len(self.indices) >= len(old.indices):
# let us suppose that:
# base[      self_start : self_stop]       = self
# 
# base[start            :            stop] = old
# 
# new = old
# 
# base[self_start] = base[start:stop][self_start - start] = old[self_start - start] = new[self_start - start]
# base[self_start + 1] = base[start:stop][self_start - start + 1] = old[self_start - start + 1] = new[self_start - start + 1]
# base[self_stop - 1] = base[start:stop][self_stop - 1 - start] = old[self_stop - 1 - start] = new[self_stop - 1 - start]
# 
# new[self_start - start: self_stop - start]
            self_indices = self.indices
            old_indices = old.indices
            
            if len(self_indices) > len(old_indices):
                shape = self.base.shape
                old_indices = [*old_indices]
                while len(self_indices) > len(old_indices): 
                    old_indices.append((0, shape[len(old_indices)]))                                                  
#             elif len(self_indices) < len(old_indices):            
#                 shape = self.base.shape
#                 self_indices = [*self_indices]
#                 while len(self_indices) < len(old_indices): 
#                     self_indices.append((0, len(self_indices)))
                                    
            indices = []
            
            for (self_start, self_stop), (start, stop) in zip(self_indices, old_indices):
                if start <= self_start and stop >= self_stop:
                    indices.append(slice(self_start - start, self_stop - start))
                else: 
                    break
            else:
                if len(indices) == 1:
                    return new[indices[0]]
                return new[tuple(indices)]
            
        return Expr._subs_slice(self, old, new, **hints)
    
    def detect_indexed(self, function):
        indexed = set()
        for expr in function.preorder_traversal():
            if expr.is_Indexed and expr.base == self.base:
                indexed.add(expr)
        return indexed
                
    @property
    def domain_bounded(self):
        base = self.base
        if base.is_Symbol: 
            from sympy import CartesianSpace
            from sympy import Interval, oo, Range 
            if 'domain' in base._assumptions:
                domain = base._assumptions['domain']
            elif base.is_positive:
                if base.is_integer:
                    domain = Range(1, oo)
                else:
                    domain = Interval(0, oo, left_open=True)
            elif base.is_negative:
                if base.is_integer:
                    domain = Range(-oo, 0)
                else:
                    domain = Interval(-oo, 0, right_open=True)
            elif base.is_nonpositive:
                if base.is_integer:
                    domain = Range(-oo, 1)
                else:
                    domain = Interval(-oo, 0)
            elif base.is_nonnegative:
                if base.is_integer:
                    domain = Range(oo)
                else:
                    domain = Interval(0, oo)
            else:
                return
            
            return CartesianSpace(domain, *self.shape)

    @property
    def is_bounded(self):
        self = self.base
        if self.is_Symbol:
            if 'domain' in self._assumptions:
                return True
#             if 'shape' in self._assumptions:
#                 return False
            
            if  'positive' in self._assumptions:
                return True
            if  'negative' in self._assumptions:
                return True
            if  'nonpositive' in self._assumptions:
                return True
            if  'nonnegative' in self._assumptions:
                return True
            if  'odd' in self._assumptions:
                return True
            if  'even' in self._assumptions:
                return True
            if  'prime' in self._assumptions:
                return True

    @property
    def unbounded(self):
        if self.is_bounded:
            return self.copy(domain=None)
        return self


class SliceIndexed(Expr):
    """Represents a mathematical object with Slices and indices both.
    in the form of x[start0:stop0, ..., start1:stop1, index0,..., index1]

    """
    is_symbol = True
    is_Atom = True

    base = property(lambda self: self.args[0])
    start = property(lambda self: self.args[1])
    stop = property(lambda self: self.args[2])

    def slices_indices(self):
        indices = self.args[1:]
        for i, arg in enumerate(indices):
            if not arg.is_Tuple:
                break
        else:
            raise Exception('SliceIndexed requires at least one index')
        
        return indices[:i], indices[i:]
    
    @property
    def slices(self):
        return self.slices_indices()[0]
     
    @property
    def indices(self):
        return self.slices_indices()[1]
    
    def copy(self, **kwargs):
        return self.base.copy(**kwargs)[self.start:self.stop]

    @property
    def distribution(self):
        distribution = self.base.distribution
        if distribution is not None:
            return distribution
                         
        definition = self.definition
        if definition is not None: 
            if self.is_integer:
                from sympy.stats.drv_types import AbstractDiscreteDistribution
                return AbstractDiscreteDistribution(definition.function)
            else: 
                from sympy.stats.crv_types import AbstractContinuousDistribution                
                return AbstractContinuousDistribution(definition) 

    def definition(self):
        definition = self.base.definition
        if definition is not None:
            return definition[self.start:self.stop]

    @property
    def domain_assumed(self):
        return self.base.domain_assumed

    @property
    def domain(self): 
        if self.dtype.is_set:
            return self.universalSet    

        from sympy import Interval, Range, CartesianSpace
        domain = self.base.domain_assumed
        if domain is None:
            assumptions = self.base.assumptions0            
            integer = assumptions.pop('integer', self.base.is_integer)
            domain = (Range if integer else Interval)(**assumptions)
            
        shape = self.shape
        if not shape:
            return domain
        return CartesianSpace(domain, *shape)

    def _dummy_eq(self, other):
        return self == other

    def structurally_equal(self, other):
        if other.is_symbol:
            return self.shape == other.shape
        return False

    # performing other in self
    def index_contains(self, other):
        if not (other.is_Indexed or other.is_Slice) or self.base != other.base: 
            return False

        start, stop = self.index
        if other.is_Slice: 
            _start, _stop = other.index
            return _start >= start and _stop <= stop
        
        if len(other.indices) > 1:
            return False

        index = other.indices[0]
        return index >= start and index < stop

    def set_comprehension(self, var=None):
        from sympy.concrete.sets import Cup

        i = self.generate_var(integer=True, var=var)
        return Cup({self.base[i]}, (i, *self.index))

    def __new__(cls, base, *args, **kw_args):
        from sympy.utilities.misc import filldedent

        if not args:
            raise IndexException("Indexed needs at least one index.")

        if len(args) == 1:
            args, *_ = args
            start, stop = args.start, args.stop
            if start is None:
                start = 0
            args = [sympify(start), sympify(stop)]
        else: 
            indices = []
            positionOfSlices = []
            positionOfIndices = []
            for i, arg in enumerate(args):
                if isinstance(arg, slice):
                    start, stop = arg.start, arg.stop
                    if start is None:
                        start = 0
                        
                    if stop is None:
                        stop = base.shape[i]
                    indices.append(Tuple(start, stop))
                    positionOfSlices.append(i)
                else:
                    arg = sympify(arg)
                    if arg.is_Tuple:
                        positionOfSlices.append(i)
                    else:
                        positionOfIndices.append(i)
                    indices.append(arg)
            assert positionOfSlices and positionOfSlices == [*range(0, len(positionOfSlices))], 'SliceIndexed requires nonempty continuous slices from the begining' 
            assert positionOfIndices and positionOfIndices == [*range(len(positionOfSlices), len(args))], 'SliceIndexed requires nonempty continuous indices up to the end'
            args = indices

        if isinstance(base, str):
            from sympy import oo
            base = Symbol(base, shape=(oo,))
        elif base.is_Symbol:
            assert len(base.shape) >= 2
        elif not hasattr(base, '__getitem__') and not isinstance(base, Symbol):
            raise TypeError(filldedent("""
                Indexed expects string, Symbol, or IndexedBase as base."""))
        elif base.is_Lamda:
            start, stop = args
            assert start != stop
            return base[start: stop]
            
        return Expr.__new__(cls, base, *args, **kw_args)

    def __iter__(self):
        raise TypeError

    @property
    def name(self):
        return str(self)

    @property
    def _diff_wrt(self):
        """Allow derivatives with respect to an ``Indexed`` object."""
        return True

    def __getitem__(self, key, **kw_args):
        if is_sequence(key):
            if len(key) == 0:
                return self

            index = key[0]
            start, stop = self.index
            base = self.base[index - start]

            if len(key) == 1:
                return base

            return base[key[1:]]
        elif isinstance(key, slice):
            start, stop = key.start, key.stop
            if start is None:
                start = 0
            if start == stop - 1:
                return self[start]
            self_start, self_stop = self.index
            start, stop = self_start + start, self_start + stop
#             assert stop <= self_stop, "try to prove, %s <= %s" % (stop, self_stop)
            return self.base[start: stop]
        else:
            (start, stop), *slices = self.slices
            base = self.base[key + start]
            if slices:
                return self.func(base, *slices, *self.indices)
            return base[self.indices]

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.functions.special.tensor_functions import KroneckerDelta
        
        if isinstance(wrt, Indexed) and wrt.base == self.base:
            if len(self.indices) != len(wrt.indices):
                msg = "Different # of indices: d({!s})/d({!s})".format(self,
                                                                       wrt)
                raise IndexException(msg)
            result = S.One
            for index1, index2 in zip(self.indices, wrt.indices):
                result *= KroneckerDelta(index1, index2)
            return result
        elif isinstance(self.base, NDimArray):
            from sympy.tensor.array import derive_by_array
            return Indexed(derive_by_array(self.base, wrt), *self.args[1:])
        else:
            if Tuple(self.indices).has(wrt):
                return S.NaN
            return S.Zero

    @property
    def rank(self):
        """
        Returns the rank of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j, k, l, m = symbols('i:m', cls=Idx)
        >>> Indexed('A', i, j).rank
        2
        >>> q = Indexed('A', i, j, k, l, m)
        >>> q.rank
        5
        >>> q.rank == len(q.indices)
        True

        """
        return len(self.args) - 1

    @property
    def shape(self):
        sizes = tuple(stop - start for start, stop in self.slices)

        numOfIndices = len(self.args) - 1
        base_length = len(self.base.shape)
        if base_length > numOfIndices: 
            sizes += self.base.shape[numOfIndices:]

        return sizes

    @property
    def ranges(self):
        """Returns a list of tuples with lower and upper range of each index.

        If an index does not define the data members upper and lower, the
        corresponding slot in the list contains ``None`` instead of a tuple.

        Examples
        ========

        >>> from sympy import Indexed,Idx, symbols
        >>> Indexed('A', Idx('i', 2), Idx('j', 4), Idx('k', 8)).ranges
        [(0, 1), (0, 3), (0, 7)]
        >>> Indexed('A', Idx('i', 3), Idx('j', 3), Idx('k', 3)).ranges
        [(0, 2), (0, 2), (0, 2)]
        >>> x, y, z = symbols('x y z', integer=True)
        >>> Indexed('A', x, y, z).ranges
        [None, None, None]

        """
        ranges = []
        for i in self.indices:
            sentinel = object()
            upper = getattr(i, 'upper', sentinel)
            lower = getattr(i, 'lower', sentinel)
            if sentinel not in (upper, lower):
                ranges.append(Tuple(lower, upper))
            else:
                ranges.append(None)
        return ranges

    def _sympystr(self, p):
        slices, indices = self.slices_indices()
        
        args = []
        for i, s in enumerate(slices):
            start, stop = s
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
            
            if stop == self.shape[i]:
                stop = ''
            else: 
                stop = p._print(stop)
                
            args.append('%s:%s' % (start, stop))
            
        args += [p._print(i) for i in indices]
            
        return "%s[%s]" % (p.doprint(self.base), ','.join(args))

    def _latex(self, p):
        slices, indices = self.slices_indices()
        
        args = []
        for i, s in enumerate(slices):
            start, stop = s
            if start.is_zero:
                start = ''
            else:
                start = p._print(start)
            
            if stop == self.shape[i]:
                stop = ''
            else: 
                stop = p._print(stop)
                
            args.append('%s:%s' % (start, stop))
            
        args += [p._print(i) for i in indices]
        return "{%s}_{%s}" % (p.doprint(self.base), ','.join(args))

    @property
    def free_symbols(self): 
        indices_free_symbols = {fs for i in self.args for fs in i.free_symbols}
        if self.base.is_Symbol:
            return {self} | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    # return exp._has(self)
    def has_match(self, exp):
        if exp.is_Indexed and exp.base == self.base:
            if len(exp.indices) == 1:

                index, *_ = exp.indices
                start, stop = self.index

                if index < start:
                    return False  # index < start
                if index >= stop:
                    return False  # index >= stop
# it is possible for them to be equal!
                return True
        if exp.is_Slice:
            if exp.base == self.base:
                index_start, index_stop = exp.index
                start, stop = self.index
    
                if index_stop <= start:
                    return False  # index < start
                if index_start >= stop:
                    return False  # index >= stop
    # it is still possible for them to be equal!
                return True
            else:
                base = exp.base.definition
                if base is not None and base._has(self):
                    return True
        return False

    def _has_matcher(self):
        """Helper for .has()"""
        return self.match

    def _has(self, pattern):
        """Helper for .has()"""
        from sympy.core.function import UndefinedFunction, Function
        if isinstance(pattern, UndefinedFunction):
            return any(f.func == pattern or f == pattern for f in self.atoms(Function, UndefinedFunction))

        pattern = sympify(pattern)
        from sympy.core.core import BasicMeta
        from sympy import preorder_traversal
        
        if isinstance(pattern, BasicMeta):
            return any(isinstance(arg, pattern) for arg in preorder_traversal(self))

        has_match = getattr(pattern, 'has_match', None)
        if has_match is not None: 
            if has_match(self):
                return True
            args = self.args[1:]
        else:
            if self == pattern:
                return True
            args = self.args

        if any(arg._has(pattern) for arg in args):
            return True
        
        definition = self.base.definition
        if definition is not None: 
            from sympy.core.symbol import Dummy
            from sympy.sets.sets import Interval
            
            k = Dummy('k', integer=True, domain=Interval(*self.index, right_open=True))
            
            return definition[k]._has(pattern)
        
        return False

    @property
    def dtype(self):
        return self.base.dtype

    def _eval_is_integer(self): 
        return self.base.is_integer

    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_complex(self):
        return self.base.is_complex

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def _eval_is_random(self):
        return self.base.is_random
    
    @property
    def is_given(self): 
        return self.base.is_given

    def as_boolean(self):
        if self.is_random:
            from sympy import Equal
            from sympy.stats.rv import pspace
            return Equal(self, pspace(self).symbol)

    def _eval_domain_defined(self, x, allow_empty=False, **_):
        domain = self.base.domain_defined(x)
        for s in self.slices:
            start, stop = s
            if allow_empty:
                domain &= x.domain_conditioned(start <= stop)
            else:
                domain &= x.domain_conditioned(start < stop)
        
        return domain


    def domain_definition(self):
        eqs = []
        for i, (start, stop) in enumerate(self.slices): 
            eqs.append((start < stop) & stop <= self.shape[i])
        from sympy import And
        return And(*eqs)        

    def _subs(self, old, new, **kwargs):
        if self == old:
            return new
        if self.base == old:
            return new[slice(*self.indices)]
        if old.is_Slice and old.base == self.base:

# base[      self_start : self_stop]       = self
# 
# base[start            :            stop] = old
# 
# new = old
# 
# base[self_start] = base[start:stop][self_start - start] = old[self_start - start] = new[self_start - start]
# base[self_start + 1] = base[start:stop][self_start - start + 1] = old[self_start - start + 1] = new[self_start - start + 1]
# base[self_stop - 1] = base[start:stop][self_stop - 1 - start] = old[self_stop - 1 - start] = new[self_stop - 1 - start]
# 
# new[self_start - start: self_stop - start]
            
            self_start, self_stop = self.index
            start, stop = old.index
            
            if start <= self_start and stop >= self_stop:
                assert new.shape
                return new[self_start - start: self_stop - start]
        return Expr._subs(self, old, new, **kwargs)


# Warning: the following class is obsolete!!! using Symbol.x(shape=(m,n,k)) instead
class IndexedBase(Expr, NotIterable):
    """Represent the base or stem of an indexed object

    The IndexedBase class represent an array that contains elements. The main purpose
    of this class is to allow the convenient creation of objects of the Indexed
    class.  The __getitem__ method of IndexedBase returns an instance of
    Indexed.  Alone, without indices, the IndexedBase class can be used as a
    notation for e.g. matrix equations, resembling what you could do with the
    Symbol class.  But, the IndexedBase class adds functionality that is not
    available for Symbol instances:

      -  An IndexedBase object can optionally store shape information.  This can
         be used in to check array conformance and conditions for numpy
         broadcasting.  (TODO)
      -  An IndexedBase object implements syntactic sugar that allows easy symbolic
         representation of array operations, using implicit summation of
         repeated indices.
      -  The IndexedBase object symbolizes a mathematical structure equivalent
         to arrays, and is recognized as such for code generation and automatic
         compilation and wrapping.

    >>> from sympy.tensor import IndexedBase, Idx
    >>> from sympy import symbols
    >>> A = IndexedBase('A'); A
    A
    >>> type(A)
    <class 'sympy.tensor.indexed.IndexedBase'>

    When an IndexedBase object receives indices, it returns an array with named
    axes, represented by an Indexed object:

    >>> i, j = symbols('i j', integer=True)
    >>> A[i, j, 2]
    A[i, j, 2]
    >>> type(A[i, j, 2])
    <class 'sympy.tensor.indexed.Indexed'>

    The IndexedBase constructor takes an optional shape argument.  If given,
    it overrides any shape information in the indices. (But not the index
    ranges!)

    >>> m, n, o, p = symbols('m n o p', integer=True)
    >>> i = Idx('i', m)
    >>> j = Idx('j', n)
    >>> A[i, j].shape
    (m, n)
    >>> B = IndexedBase('B', shape=(o, p))
    >>> B[i, j].shape
    (o, p)

    Assumptions can be specified with keyword arguments the same way as for Symbol:

    >>> A_real = IndexedBase('A', real=True)
    >>> A_real.is_real
    True
    >>> A != A_real
    True

    Assumptions can also be inherited if a Symbol is used to initialize the IndexedBase:

    >>> I = symbols('I', integer=True)
    >>> C_inherit = IndexedBase(I)
    >>> C_explicit = IndexedBase('I', integer=True)
    >>> C_inherit == C_explicit
    True
    """
    is_commutative = True
    is_symbol = True
    is_Atom = True

    @staticmethod
    def _set_assumptions(obj, assumptions):
        """Set assumptions on obj, making sure to apply consistent values."""
        tmp_asm_copy = assumptions.copy()
        is_commutative = fuzzy_bool(assumptions.get('commutative', True))
        assumptions['commutative'] = is_commutative
        obj._assumptions = StdFactKB(assumptions)
        obj._assumptions._generator = tmp_asm_copy  # Issue #8873

    def __new__(cls, label, shape=None, *, offset=S.Zero, strides=None, **kw_args):
        from sympy import MatrixBase, NDimArray

        assumptions, kw_args = _filter_assumptions(kw_args)
        if isinstance(label, str):
            label = Symbol(label, **assumptions)
        elif isinstance(label, Symbol):
            assumptions = label._merge(assumptions)
        elif isinstance(label, (MatrixBase, NDimArray)):
            return label
        elif isinstance(label, Iterable):
            return _sympify(label)
        else:
            label = _sympify(label)

        if is_sequence(shape):
            shape = Tuple(*shape)
        elif shape is not None:
            shape = Tuple(shape)

        if shape is not None:
            obj = Expr.__new__(cls, label, shape)
        else:
            obj = Expr.__new__(cls, label)
        obj._shape = shape
        obj._offset = offset
        obj._strides = strides
        obj._name = str(label)

        IndexedBase._set_assumptions(obj, assumptions)
        return obj

    @property
    def name(self):
        return self._name

    def _hashable_content(self):
        return super(IndexedBase, self)._hashable_content() + tuple(sorted(self.assumptions0.items()))

    @property
    def assumptions0(self):
        return {k: v for k, v in self._assumptions.items() if v is not None}

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            # Special case needed because M[*my_tuple] is a syntax error.
            if self.shape and len(self.shape) != len(indices):
                raise IndexException("Rank mismatch.")
            return Indexed(self, *indices, **kw_args)
        else:
            if self.shape and len(self.shape) != 1:
                raise IndexException("Rank mismatch.")
            return Indexed(self, indices, **kw_args)

    @property
    def shape(self):
        """Returns the shape of the ``IndexedBase`` object.

        Examples
        ========

        >>> from sympy import IndexedBase, Idx
        >>> from sympy.abc import x, y
        >>> IndexedBase('A', shape=(x, y)).shape
        (x, y)

        Note: If the shape of the ``IndexedBase`` is specified, it will override
        any shape information given by the indices.

        >>> A = IndexedBase('A', shape=(x, y))
        >>> B = IndexedBase('B')
        >>> i = Idx('i', 2)
        >>> j = Idx('j', 1)
        >>> A[i, j].shape
        (x, y)
        >>> B[i, j].shape
        (2, 1)

        """
        return self._shape

    @property
    def strides(self):
        """Returns the strided scheme for the ``IndexedBase`` object.

        Normally this is a tuple denoting the number of
        steps to take in the respective dimension when traversing
        an array. For code generation purposes strides='C' and
        strides='F' can also be used.

        strides='C' would mean that code printer would unroll
        in row-major order and 'F' means unroll in column major
        order.

        """

        return self._strides

    @property
    def offset(self):
        """Returns the offset for the ``IndexedBase`` object.

        This is the value added to the resulting index when the
        2D Indexed object is unrolled to a 1D form. Used in code
        generation.

        Examples
        ==========
        >>> from sympy.printing import ccode
        >>> from sympy.tensor import IndexedBase, Idx
        >>> from sympy import symbols
        >>> l, m, n, o = symbols('l m n o', integer=True)
        >>> A = IndexedBase('A', strides=(l, m, n), offset=o)
        >>> i, j, k = map(Idx, 'ijk')
        >>> ccode(A[i, j, k])
        'A[l*i + m*j + n*k + o]'

        """
        return self._offset

    @property
    def label(self):
        """Returns the label of the ``IndexedBase`` object.

        Examples
        ========

        >>> from sympy import IndexedBase
        >>> from sympy.abc import x, y
        >>> IndexedBase('A', shape=(x, y)).label
        A

        """
        return self.args[0]

    def _sympystr(self, p):
        return p.doprint(self.label)


class Idx(Expr):
    """Represents an integer index as an ``Integer`` or integer expression.

    There are a number of ways to create an ``Idx`` object.  The constructor
    takes two arguments:

    ``label``
        An integer or a symbol that labels the index.
    ``range``
        Optionally you can specify a range as either

        * ``Symbol`` or integer: This is interpreted as a dimension. Lower and
          upper bounds are set to ``0`` and ``range - 1``, respectively.
        * ``tuple``: The two elements are interpreted as the lower and upper
          bounds of the range, respectively.

    Note: bounds of the range are assumed to be either integer or infinite (oo
    and -oo are allowed to specify an unbounded range). If ``n`` is given as a
    bound, then ``n.is_integer`` must not return false.

    For convenience, if the label is given as a string it is automatically
    converted to an integer symbol.  (Note: this conversion is not done for
    range or dimension arguments.)

    Examples
    ========

    >>> from sympy import IndexedBase, Idx, symbols, oo
    >>> n, i, L, U = symbols('n i L U', integer=True)

    If a string is given for the label an integer ``Symbol`` is created and the
    bounds are both ``None``:

    >>> idx = Idx('qwerty'); idx
    qwerty
    >>> idx.lower, idx.upper
    (None, None)

    Both upper and lower bounds can be specified:

    >>> idx = Idx(i, (L, U)); idx
    i
    >>> idx.lower, idx.upper
    (L, U)

    When only a single bound is given it is interpreted as the dimension
    and the lower bound defaults to 0:

    >>> idx = Idx(i, n); idx.lower, idx.upper
    (0, n - 1)
    >>> idx = Idx(i, 4); idx.lower, idx.upper
    (0, 3)
    >>> idx = Idx(i, oo); idx.lower, idx.upper
    (0, oo)

    """

    is_integer = True
    is_finite = True
    is_real = True
    is_symbol = True
    is_Atom = True
    _diff_wrt = True

    def __new__(cls, label, range=None, **kw_args):
        from sympy.utilities.misc import filldedent

        if isinstance(label, str):
            label = Symbol(label, integer=True)
        label, range = list(map(sympify, (label, range)))

        if label.is_Number:
            if not label.is_integer:
                raise TypeError("Index is not an integer number.")
            return label

        if not label.is_integer:
            raise TypeError("Idx object requires an integer label.")

        elif is_sequence(range):
            if len(range) != 2:
                raise ValueError(filldedent("""
                    Idx range tuple must have length 2, but got %s""" % len(range)))
            for bound in range:
                if (bound.is_integer == False and bound is not S.Infinity
                        and bound is not S.NegativeInfinity):
                    raise TypeError("Idx object requires integer bounds.")
            args = label, Tuple(*range)
        elif isinstance(range, Expr):
            if not (range.is_integer or range is S.Infinity):
                raise TypeError("Idx object requires an integer dimension.")
            args = label, Tuple(0, range - 1)
        elif range:
            raise TypeError(filldedent("""
                The range must be an ordered iterable or
                integer SymPy expression."""))
        else:
            args = label,

        obj = Expr.__new__(cls, *args, **kw_args)
        obj._assumptions["finite"] = True
        obj._assumptions["real"] = True
        return obj

    @property
    def label(self):
        """Returns the label (Integer or integer expression) of the Idx object.

        Examples
        ========

        >>> from sympy import Idx, Symbol
        >>> x = Symbol('x', integer=True)
        >>> Idx(x).label
        x
        >>> j = Symbol('j', integer=True)
        >>> Idx(j).label
        j
        >>> Idx(j + 1).label
        j + 1

        """
        return self.args[0]

    @property
    def lower(self):
        """Returns the lower bound of the ``Idx``.

        Examples
        ========

        >>> from sympy import Idx
        >>> Idx('j', 2).lower
        0
        >>> Idx('j', 5).lower
        0
        >>> Idx('j').lower is None
        True

        """
        try:
            return self.args[1][0]
        except IndexError:
            return

    @property
    def upper(self):
        """Returns the upper bound of the ``Idx``.

        Examples
        ========

        >>> from sympy import Idx
        >>> Idx('j', 2).upper
        1
        >>> Idx('j', 5).upper
        4
        >>> Idx('j').upper is None
        True

        """
        try:
            return self.args[1][1]
        except IndexError:
            return

    def _sympystr(self, p):
        return p.doprint(self.label)

    @property
    def name(self):
        return self.label.name if self.label.is_Symbol else str(self.label)

    @property
    def free_symbols(self):
        return {self}

    def __le__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.upper is not None and (self.upper <= other_lower) == True:
            return True
        if self.lower is not None and (self.lower > other_upper) == True:
            return False
        return super(Idx, self).__le__(other)

    def __ge__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.lower is not None and (self.lower >= other_upper) == True:
            return True
        if self.upper is not None and (self.upper < other_lower) == True:
            return False
        return super(Idx, self).__ge__(other)

    def __lt__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.upper is not None and (self.upper < other_lower) == True:
            return True
        if self.lower is not None and (self.lower >= other_upper) == True:
            return False
        return super(Idx, self).__lt__(other)

    def __gt__(self, other):
        if isinstance(other, Idx):
            other_upper = other if other.upper is None else other.upper
            other_lower = other if other.lower is None else other.lower
        else:
            other_upper = other
            other_lower = other

        if self.lower is not None and (self.lower > other_upper) == True:
            return True
        if self.upper is not None and (self.upper <= other_lower) == True:
            return False
        return super(Idx, self).__gt__(other)

