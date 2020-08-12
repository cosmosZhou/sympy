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

from __future__ import print_function, division

from sympy.core import Expr, Tuple, Symbol, sympify, S
from sympy.core.compatibility import (is_sequence, string_types, NotIterable,
                                      Iterable)
from sympy.core.sympify import _sympify
from sympy.functions.special.tensor_functions import KroneckerDelta


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
    is_Indexed = True
    is_symbol = True
    is_Atom = True

    @classmethod
    def class_key(cls):
        return 3, 0, cls.__name__

    def __iter__(self):
        raise TypeError

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            indices = self.indices + tuple(indices)
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            if start == 0 and stop == self.shape[-1]:
                return self
            return Slice(self, indices, **kw_args)
        else:
            indices = self.indices + (indices,)
            
        assert len(indices) <= len(self.base.shape)
        return Indexed(self.base, *indices, **kw_args)

    def image_set(self):
        definition = self.base.definition
        if definition is None:
            return None
        return definition[self.indices].image_set()

    def element_symbol(self, excludes=set()):
        element_type = self.element_type
        if element_type is None:
            return

        return self.generate_free_symbol(excludes=excludes, **element_type.dict)

    # performing other in self
    def __contains__(self, other):
        if other == self:
            return True
        if self.base.definition is not None:
            return other in self.base.definition[self.indices]

    @property
    def is_integer(self):
        if self.base.definition is not None:
            return self.base.definition.is_integer 
        return self.base.is_integer

    def _dummy_eq(self, other):
        return self == other

    def structure_eq(self, other):
        if isinstance(other, (Symbol, Indexed, Slice)):
            return self.shape == other.shape
        return False

    def __new__(cls, base, *args, **kw_args):
        from sympy.utilities.misc import filldedent
        from sympy.tensor.array.ndim_array import NDimArray
        from sympy.matrices.matrices import MatrixBase

        if not args:
            return base
#             raise IndexException("Indexed needs at least one index.")
        if isinstance(base, string_types):
            base = Symbol(base, shape=(S.Infinity,))
        elif isinstance(base, Symbol):
            assert base.shape
        elif not hasattr(base, '__getitem__') and not base.is_Symbol:
            raise TypeError(filldedent("Indexed expects string, Symbol as base."))
        args = list(map(sympify, args))
        if isinstance(base, (NDimArray, Tuple, MatrixBase)) and all([i.is_number for i in args]):
            if len(args) == 1:
                return base[args[0]]
            else:
                return base[args]
            
        if len(args) == 1 and args[0].is_Piecewise:
            piecewise = args[0]
            return piecewise.func(*((Indexed(base, e), c) for e, c in piecewise.args))
            
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
        return self.base.dtype[self.indices].is_set

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray

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
    def base(self):
        """Returns the ``IndexedBase`` of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, IndexedBase, Idx, symbols
        >>> i, j = symbols('i j', cls=Idx)
        >>> Indexed('A', i, j).base
        A
        >>> B = IndexedBase('B')
        >>> B == B[i, j].base
        True

        """
        return self.args[0]

    @property
    def indices(self):
        """
        Returns the indices of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j = symbols('i j', cls=Idx)
        >>> Indexed('A', i, j).indices
        (i, j)

        """
        return self.args[1:]

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
        """Returns a list with dimensions of each index.

        Dimensions is a property of the array, not of the indices.  Still, if
        the ``IndexedBase`` does not define a shape attribute, it is assumed
        that the ranges of the indices correspond to the shape of the array.

        >>> from sympy import IndexedBase, Idx, symbols
        >>> n, m = symbols('n m', integer=True)
        >>> i = Idx('i', m)
        >>> j = Idx('j', m)
        >>> A = IndexedBase('A', shape=(n, n))
        >>> B = IndexedBase('B')
        >>> A[i, j].shape
        (n, n)
        >>> B[i, j].shape
        (m, m)
        """
        try:
            return self.base.shape[len(self.indices):]
        except:
            print(self.base)
            print(self.base.shape)
#         from sympy.utilities.misc import filldedent
#
#         if self.base.shape:
#             return self.base.shape
#         sizes = []
#         for i in self.indices:
#             upper = getattr(i, 'upper', None)
#             lower = getattr(i, 'lower', None)
#             if None in (upper, lower):
#                 raise IndexException(filldedent("""
#                     Range is not defined for all indices in: %s""" % self))
#             try:
#                 size = upper - lower + 1
#             except TypeError:
#                 raise IndexException(filldedent("""
#                     Shape cannot be inferred from Idx with
#                     undefined range: %s""" % self))
#             sizes.append(size)
#         return Tuple(*sizes)

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

    @property
    def free_symbols(self):
        base_free_symbols = self.base.free_symbols
        indices_free_symbols = {
            fs for i in self.indices for fs in i.free_symbols}
        if base_free_symbols:
            return {self} | base_free_symbols | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    def has_match(self, exp):
        from sympy.matrices.expressions.matexpr import MatrixElement
        if isinstance(exp, MatrixElement) and exp.parent == self.base:
            return True
        from sympy.core.symbol import Wild
        if isinstance(exp, Indexed) and exp.base == self.base:
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

        if isinstance(exp, Slice) and exp.base == self.base:
            if len(self.indices) == 1:
                start, stop = exp.indices
                index_fixed, *_ = self.indices

                if isinstance(index_fixed, Wild):
                    return False

                if stop <= index_fixed:
                    return False
                if start > index_fixed:
                    return False
                # it is possible for them to be equal!
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
        """Helper for .has()"""
        if any(arg._has(pattern) for arg in self.indices):
            return True
        from sympy.core.assumptions import ManagedProperties
        
        if not isinstance(pattern, ManagedProperties) and hasattr(pattern, 'has_match') and pattern.has_match(self):
            return True
            
        from sympy.core.function import FunctionClass
        
        if not isinstance(pattern, (FunctionClass, ManagedProperties)):
            if self.base.definition is not None:
                return self.base.definition[self.indices]._has(pattern)
            if self.base.is_Transpose:
                if self.base.arg == pattern:
                    return True
        
        return False

    def _subs(self, old, new, **_):
        if self.base == old:
            return new[self.indices]
        if isinstance(old, Slice) and old.base == self.base and len(self.indices) == 1:
            k = self.indices[0]
            start, stop = old.indices
            if k >= start and k < stop:
                return new[k - start]
        return Expr._subs(self, old, new)

    @property
    def pspace(self):
        from sympy.stats.crv import SingleContinuousPSpace
        from sympy.stats.crv_types import AbstractDistribution
        from sympy.stats.rv import RandomSymbol
        definition = self.base.definition[self.indices]
        if isinstance(definition, RandomSymbol):
            return definition.pspace        
        return SingleContinuousPSpace(self.base.copy(shape=self.base.shape, real=self.base.is_real, integer=self.base.is_integer)[self.indices], AbstractDistribution(definition))

    def is_random_symbol(self):
        from sympy.stats.rv import RandomSymbol
        from sympy.stats.rv import contain_random_symbols
        if 'definition' in self.base._assumptions:
            if self.base.definition.is_Ref and len(self.base.definition.limits) == len(self.indices):
                definition = self.base.definition.function
                if isinstance(definition, RandomSymbol) or contain_random_symbols(definition):
                    return True
        return False

    @property
    def atomic_dtype(self):
        return self.base.atomic_dtype

    def domain_defined(self, x):
        from sympy.sets.sets import Interval
        for i, index in enumerate(self.indices):
            if not x.shape and index._has(x):
                diff = x - index
                if diff.free_symbols & index.free_symbols:
                    continue
                return Interval(diff, self.base.shape[i] - 1 + diff, integer=True)
        if self.base.definition is not None:
            return self.base.definition[self.indices].domain_defined(x)
        
        if x.atomic_dtype.is_set:
            return S.UniversalSet
        domain = x.domain          
         
        for index in self.indices:
            domain &= index.domain_defined(x)
        return domain

#     def __iter__(self):
#         raise TypeError

    @property
    def definition(self):
        return self.base.definition[self.indices]
    
    def _eval_is_extended_real(self):
        return self.base.is_extended_real

    def _eval_is_extended_negative(self):
        return self.base.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.base.is_extended_positive

    def _eval_is_finite(self):
        return self.base.is_finite

    def _eval_is_zero(self):
        return self.base.is_zero

    def copy(self, **kwargs):
        return self.base.copy(shape=self.base.shape, **kwargs)[self.indices]

class Slice(Expr):
    """Represents a mathematical object with Slices.

    """
    is_commutative = True
    is_Indexed = True
    is_symbol = True
    is_Atom = True
    is_Slice = True

    def _dummy_eq(self, other):
        return self == other

    def structure_eq(self, other):
        if isinstance(other, (Symbol, Indexed, IndexedBase, Slice)):
            return self.shape == other.shape
        return False

    # performing other in self
    def __contains__(self, other):
        if not other.is_Indexed or self.base != other.base:
            return False

        if other.is_Slice:
            start, stop = self.indices
            _start, _stop = other.indices
            return _start >= start and _stop <= stop
        if len(self.indices) > 1:
            return False

        index = self.indices[0]
        return index >= start and index < stop

    @property
    def set(self):
        from sympy.concrete.expr_with_limits import UnionComprehension

        i = self.generate_free_symbol(integer=True)
        start, stop = self.indices
        return UnionComprehension({self.base[i]}, (i, start, stop - 1))

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

        if isinstance(base, Symbol):
            assert base.shape
        elif isinstance(base, string_types):
            from sympy import oo
            base = Symbol(base, shape=(oo,))
        elif not hasattr(base, '__getitem__') and not isinstance(base, IndexedBase):
            raise TypeError(filldedent("""
                Indexed expects string, Symbol, or IndexedBase as base."""))
        elif base.is_Ref:
            start, stop = args
            return base[start : stop]

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

    def __getitem__(self, indices, **kw_args):
        if is_sequence(indices):
            if len(indices) == 0:
                return self

            index = indices[0]
            start, stop = self.indices
            base = self.base[index - start]

            if len(indices) == 1:
                return base

            return base[indices[1:]]
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            if start == stop - 1:
                return self[start]
            return Slice(self, indices, **kw_args)
        else:
            start, stop = self.indices
            return self.base[indices - start]

    def _eval_derivative(self, wrt):
        from sympy.tensor.array.ndim_array import NDimArray

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
    def base(self):
        """Returns the ``IndexedBase`` of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, IndexedBase, Idx, symbols
        >>> i, j = symbols('i j', cls=Idx)
        >>> Indexed('A', i, j).base
        A
        >>> B = IndexedBase('B')
        >>> B == B[i, j].base
        True

        """
        return self.args[0]

    @property
    def indices(self):
        """
        Returns the indices of the ``Indexed`` object.

        Examples
        ========

        >>> from sympy import Indexed, Idx, symbols
        >>> i, j = symbols('i j', cls=Idx)
        >>> Indexed('A', i, j).indices
        (i, j)

        """
        return self.args[1:]

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
        """Returns a list with dimensions of each index.

        Dimensions is a property of the array, not of the indices.  Still, if
        the ``IndexedBase`` does not define a shape attribute, it is assumed
        that the ranges of the indices correspond to the shape of the array.

        >>> from sympy import IndexedBase, Idx, symbols
        >>> n, m = symbols('n m', integer=True)
        >>> i = Idx('i', m)
        >>> j = Idx('j', m)
        >>> A = IndexedBase('A', shape=(n, n))
        >>> B = IndexedBase('B')
        >>> A[i, j].shape
        (n, n)
        >>> B[i, j].shape
        (m, m)
        """

        sizes = []
        start, stop = self.indices
        sizes.append(stop - start)

        if len(self.base.shape) > len(sizes):
            sizes += [self.base.shape[i] for i in range(len(sizes), len(self.base.shape))]

        return Tuple(*sizes)

#     def __len__(self):
#         start, stop = self.indices
#         return stop - start

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
        return "%s[%s]" % (p.doprint(self.base), ":".join(indices))

    @property
    def free_symbols(self):
        base_free_symbols = self.base.free_symbols
        indices_free_symbols = {
            fs for i in self.indices for fs in i.free_symbols}
        if base_free_symbols:
            return {self} | base_free_symbols | indices_free_symbols
        else:
            return indices_free_symbols

    @property
    def expr_free_symbols(self):
        return {self}

    def bisect(self, front=None, back=None):
        start, stop = self.indices
        length = stop - start
        if front is not None:
            back = length - front
        else:
            front = length - back

        return self.base[start:stop - back], self.base[stop - back: stop]

    def has_match(self, exp):
        from sympy.matrices.expressions.matexpr import MatrixElement
        if isinstance(exp, MatrixElement) and exp.parent == self.base:
            return True
        if isinstance(exp, Indexed) and exp.base == self.base:
            if len(exp.indices) == 1:

                index, *_ = exp.indices
                start, stop = self.indices

                if index < start:
                    return False  # index < start
                if index >= stop:
                    return False  # index >= stop
# it is possible for them to be equal!
                return True
        if isinstance(exp, Slice) and exp.base == self.base:
            index_start, index_stop = exp.indices
            start, stop = self.indices

            if index_stop <= start:
                return False  # index < start
            if index_start >= stop:
                return False  # index >= stop
# it is possible for them to be equal!
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

        return any(arg._has(pattern) for arg in args)

    @property
    def atomic_dtype(self):
        return self.base.atomic_dtype


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

        if isinstance(label, string_types):
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
                if (bound.is_integer is False and bound is not S.Infinity
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


def linear_transformation(trafo, limit):
    var, lower, upper = limit
    p = trafo.as_poly(var)
    if p.degree() == 1:
        alpha = p.coeff_monomial(var)
        beta = p.coeff_monomial(S.One)
        if alpha.is_number:
            if alpha == S.One:
                return alpha * lower + beta, alpha * upper + beta
            elif alpha == S.NegativeOne:
                return alpha * upper + beta, alpha * lower + beta
    return None, None
