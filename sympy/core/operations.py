from operator import attrgetter 
from collections import defaultdict

from sympy.utilities.exceptions import SymPyDeprecationWarning

from sympy.core.sympify import _sympify as _sympify_, sympify
from sympy.core.basic import Basic
from sympy.core.cache import cacheit
from sympy.core.compatibility import ordered, default_sort_key
from sympy.core.logic import _fuzzy_group
from sympy.core.parameters import global_parameters
from sympy.utilities.iterables import sift
from sympy.multipledispatch.dispatcher import (Dispatcher,
    ambiguity_register_error_ignore_dup,
    str_signature, RaiseNotImplementedError)
from sympy.core.containers import Tuple


class AssocOp(Basic):
    """ Associative operations, can separate noncommutative and commutative parts.

    (a op b) op c == a op (b op c) == a op b op c.

    Base class for Add and Mul.

    This is an abstract base class, concrete derived classes must define
    the attribute `identity`.

    Parameters
    ==========

    *args :
        Arguments which are operated

    evaluate : bool, optional
        Evaluate the operation. If not passed, refer to ``global_parameters.evaluate``.
    """

    # for performance reason, we don't let is_commutative go to assumptions,
    # and keep it right here
    __slots__ = ('is_commutative',)  # type: Tuple[str, ...]

    _args_type = None  # type: Type[Basic]

    @cacheit
    def __new__(cls, *args, evaluate=None, _sympify=True):
        # Allow faster processing by passing ``_sympify=False``, if all arguments
        # are already sympified.
        if _sympify:
            args = list(map(_sympify_, args))

        # Disallow non-Expr args in Add/Mul
        typ = cls._args_type
        if typ is not None:
            from sympy.core.relational import Relational
            if any(isinstance(arg, Relational) for arg in args):
                raise TypeError("Relational can not be used in %s" % cls.__name__)

            # This should raise TypeError once deprecation period is over:
            if not all(isinstance(arg, typ) for arg in args):
                SymPyDeprecationWarning(
                    feature="Add/Mul with non-Expr args",
                    useinstead="Expr args",
                    issue=19445,
                    deprecated_since_version="1.7"
                ).warn()

        args = [a for a in args if a is not cls.identity]
        # sifting so here to simplify the result
        if evaluate is None:
            evaluate = global_parameters.evaluate
        if not evaluate:
            obj = cls._from_args(args)
            obj = cls._exec_constructor_postprocessors(obj)
            return obj

        if len(args) == 0:
            return cls.identity
        if len(args) == 1:
            return args[0]

        c_part, nc_part, other_symbols = cls.flatten(args)
        is_commutative = not nc_part
        obj = cls._from_args(c_part + nc_part, is_commutative)

        if other_symbols is not None:
            if isinstance(other_symbols, tuple):
                from sympy.series.order import Order
                return Order(obj, *other_symbols)
            assert other_symbols.infinitesimality is not None
            return obj + other_symbols
        return obj

    @property
    def dtype(self):
        dtype = None
        for arg in self.args:
            _dtype = arg.dtype
            if dtype is None:
                dtype = _dtype
                continue
            
            if dtype in _dtype:
                dtype = _dtype
        return dtype

    @classmethod
    def _from_args(cls, args, is_commutative=None):
        """Create new instance with already-processed args.
        If the args are not in canonical order, then a non-canonical
        result will be returned, so use with caution. The order of
        args may change if the sign of the args is changed."""
        if len(args) == 0:
            return cls.identity
        elif len(args) == 1:
            return args[0]

        args = tuple(ordered(args, default_sort_key))

        obj = super(AssocOp, cls).__new__(cls, *args)
        return obj

    def _new_rawargs(self, *args, **kwargs):
        """Create new instance of own class with args exactly as provided by
        caller but returning the self class identity if args is empty.

        Examples
        ========

           This is handy when we want to optimize things, e.g.

               >>> from sympy import Mul, S
               >>> from sympy.abc import x, y
               >>> e = Mul(3, x, y)
               >>> e.args
               (3, x, y)
               >>> Mul(*e.args[1:])
               x*y
               >>> e._new_rawargs(*e.args[1:])  # the same as above, but faster
               x*y

           Note: use this with caution. There is no checking of arguments at
           all. This is best used when you are rebuilding an Add or Mul after
           simply removing one or more args. If, for example, modifications,
           result in extra 1s being inserted they will show up in the result:

               >>> m = (x*y)._new_rawargs(S.One, x); m
               1*x
               >>> m == x
               False
               >>> m.is_Mul
               True

           Another issue to be aware of is that the commutativity of the result
           is based on the commutativity of self. If you are rebuilding the
           terms that came from a commutative object then there will be no
           problem, but if self was non-commutative then what you are
           rebuilding may now be commutative.

           Although this routine tries to do as little as possible with the
           input, getting the commutativity right is important, so this level
           of safety is enforced: commutativity will always be recomputed if
           self is non-commutative and kwarg `reeval=False` has not been
           passed.
        """
#         if kwargs.pop('reeval', True) and self.is_commutative == False:
#             is_commutative = None
#         else:
#             is_commutative = self.is_commutative
        return self._from_args(args, is_commutative=True)

    @classmethod
    def flatten(cls, seq):
        """Return seq so that none of the elements are of type `cls`. This is
        the vanilla routine that will be used if a class derived from AssocOp
        does not define its own flatten routine."""
        # apply associativity, no commutativity property is used
        new_seq = []
        while seq:
            o = seq.pop()
            if o.__class__ is cls:  # classes must match exactly
                seq.extend(o.args)
            else:
                new_seq.append(o)
        new_seq.reverse()

        # c_part, nc_part, order_symbols
        return [], new_seq, None

    def _matches_commutative(self, expr, repl_dict={}, old=False):
        """
        Matches Add/Mul "pattern" to an expression "expr".

        repl_dict ... a dictionary of (wild: expression) pairs, that get
                      returned with the results

        This function is the main workhorse for Add/Mul.

        Examples
        ========

        >>> from sympy import symbols, Wild, sin
        >>> a = Wild("a")
        >>> b = Wild("b")
        >>> c = Wild("c")
        >>> x, y, z = symbols("x y z")
        >>> (a+sin(b)*c)._matches_commutative(x+sin(y)*z)
        {a_: x, b_: y, c_: z}

        In the example above, "a+sin(b)*c" is the pattern, and "x+sin(y)*z" is
        the expression.

        The repl_dict contains parts that were already matched. For example
        here:

        >>> (x+sin(b)*c)._matches_commutative(x+sin(y)*z, repl_dict={a: x})
        {a_: x, b_: y, c_: z}

        the only function of the repl_dict is to return it in the
        result, e.g. if you omit it:

        >>> (x+sin(b)*c)._matches_commutative(x+sin(y)*z)
        {b_: y, c_: z}

        the "a: x" is not returned in the result, but otherwise it is
        equivalent.

        """
        # make sure expr is Expr if pattern is Expr
        from .expr import Add, Expr
        from sympy import Mul
        repl_dict = repl_dict.copy()
        if isinstance(self, Expr) and not isinstance(expr, Expr):
            return None

        # handle simple patterns
        if self == expr:
            return repl_dict

        d = self._matches_simple(expr, repl_dict)
        if d is not None:
            return d

        # eliminate exact part from pattern: (2+a+w1+w2).matches(expr) -> (w1+w2).matches(expr-a-2)
        from .function import WildFunction
        from .symbol import Wild
        wild_part, exact_part = sift(self.args, lambda p:
            p.has(Wild, WildFunction) and not expr.has(p),
            binary=True)
        if not exact_part:
            wild_part = list(ordered(wild_part))
            if self.is_Add:
                # in addition to normal ordered keys, impose
                # sorting on Muls with leading Number to put
                # them in order
                wild_part = sorted(wild_part, key=lambda x:
                    x.args[0] if x.is_Mul and x.args[0].is_Number else
                    0)
        else:
            exact = self._new_rawargs(*exact_part)
            free = expr.free_symbols
            if free and (exact.free_symbols - free):
                # there are symbols in the exact part that are not
                # in the expr; but if there are no free symbols, let
                # the matching continue
                return None
            newexpr = self._combine_inverse(expr, exact)
            if not old and (expr.is_Add or expr.is_Mul):
                if newexpr.count_ops() > expr.count_ops():
                    return None
            newpattern = self._new_rawargs(*wild_part)
            return newpattern.matches(newexpr, repl_dict)

        # now to real work ;)
        i = 0
        saw = set()
        while expr not in saw:
            saw.add(expr)
            args = tuple(ordered(self.make_args(expr)))
            if self.is_Add and expr.is_Add:
                # in addition to normal ordered keys, impose
                # sorting on Muls with leading Number to put
                # them in order
                args = tuple(sorted(args, key=lambda x:
                    x.args[0] if x.is_Mul and x.args[0].is_Number else
                    0))
            expr_list = (self.identity,) + args
            for last_op in reversed(expr_list):
                for w in reversed(wild_part):
                    d1 = w.matches(last_op, repl_dict)
                    if d1 is not None:
                        d2 = self.xreplace(d1).matches(expr, d1)
                        if d2 is not None:
                            return d2

            if i == 0:
                if self.is_Mul:
                    # make e**i look like Mul
                    if expr.is_Pow and expr.exp.is_Integer:
                        if expr.exp > 0:
                            expr = Mul(*[expr.base, expr.base ** (expr.exp - 1)], evaluate=False)
                        else:
                            expr = Mul(*[1 / expr.base, expr.base ** (expr.exp + 1)], evaluate=False)
                        i += 1
                        continue

                elif self.is_Add:
                    # make i*e look like Add
                    c, e = expr.as_coeff_Mul()
                    if abs(c) > 1:
                        if c > 0:
                            expr = Add(*[e, (c - 1) * e], evaluate=False)
                        else:
                            expr = Add(*[-e, (c + 1) * e], evaluate=False)
                        i += 1
                        continue

                    # try collection on non-Wild symbols
                    from sympy.simplify.radsimp import collect
                    was = expr
                    did = set()
                    for w in reversed(wild_part):
                        c, w = w.as_coeff_mul(Wild)
                        free = c.free_symbols - did
                        if free:
                            did.update(free)
                            expr = collect(expr, free)
                    if expr != was:
                        i += 0
                        continue

                break  # if we didn't continue, there is nothing more to do

        return

    def _has_matcher(self):
        """Helper for .has()"""

        def _ncsplit(expr):
            # this is not the same as args_cnc because here
            # we don't assume expr is a Mul -- hence deal with args --
            # and always return a set.
            cpart, ncpart = sift(expr.args,
                lambda arg: arg.is_commutative == True, binary=True)
            return set(cpart), ncpart

        c, nc = _ncsplit(self)
        cls = self.__class__

        def is_in(expr):
            if expr == self:
                return True
            elif not isinstance(expr, Basic):
                return False
            elif isinstance(expr, cls):
                _c, _nc = _ncsplit(expr)
                if (c & _c) == c:
                    if not nc:
                        return True
                    elif len(nc) <= len(_nc):
                        for i in range(len(_nc) - len(nc) + 1):
                            if _nc[i:i + len(nc)] == nc:
                                return True
            return False

        return is_in

    def _eval_evalf(self, prec):
        """
        Evaluate the parts of self that are numbers; if the whole thing
        was a number with no functions it would have been evaluated, but
        it wasn't so we must judiciously extract the numbers and reconstruct
        the object. This is *not* simply replacing numbers with evaluated
        numbers. Numbers should be handled in the largest pure-number
        expression as possible. So the code below separates ``self`` into
        number and non-number parts and evaluates the number parts and
        walks the args of the non-number part recursively (doing the same
        thing).
        """
        from .add import Add
        from .mul import Mul
        from .symbol import Symbol
        from .function import AppliedUndef
        if isinstance(self, (Mul, Add)):
            x, tail = self.as_independent(Symbol, AppliedUndef)
            # if x is an AssocOp Function then the _evalf below will
            # call _eval_evalf (here) so we must break the recursion
            if not (tail is self.identity or
                    isinstance(x, AssocOp) and x.is_Function or
                    x is self.identity and isinstance(tail, AssocOp)):
                # here, we have a number so we just call to _evalf with prec;
                # prec is not the same as n, it is the binary precision so
                # that's why we don't call to evalf.
                x = x._evalf(prec) if x is not self.identity else self.identity
                args = []
                tail_args = tuple(self.func.make_args(tail))
                for a in tail_args:
                    # here we call to _eval_evalf since we don't know what we
                    # are dealing with and all other _eval_evalf routines should
                    # be doing the same thing (i.e. taking binary prec and
                    # finding the evalf-able args)
                    newa = a._eval_evalf(prec)
                    if newa is None:
                        args.append(a)
                    else:
                        args.append(newa)
                return self.func(x, *args)

        # this is the same as above, but there were no pure-number args to
        # deal with
        args = []
        for a in self.args:
            newa = a._eval_evalf(prec)
            if newa is None:
                args.append(a)
            else:
                args.append(newa)
        return self.func(*args)

    @classmethod
    def make_args(cls, expr):
        """
        Return a sequence of elements `args` such that cls(*args) == expr

        Examples
        ========

        >>> from sympy import Symbol, Mul, Add
        >>> x, y = map(Symbol, 'xy')

        >>> Mul.make_args(x*y)
        (x, y)
        >>> Add.make_args(x*y)
        (x*y,)
        >>> set(Add.make_args(x*y + y)) == set([y, x*y])
        True

        """
        if isinstance(expr, cls):
            return expr.args
        else:
            return (sympify(expr),)

    def doit(self, **hints):
        if hints.get('deep', True):
            args = [arg.doit(**hints) for arg in self.args]
            hit = False
            len_shape = len(self.shape)
            for arg in args:
                if arg.is_DenseMatrix:
                    if len(arg.shape) == len_shape:
                        hit = True
            if hit:
                from sympy import Matrix
                if len_shape == 1:
                    n, = self.shape
                    return Matrix(tuple(self[i] for i in range(n)))
                if len_shape == 2:
                    m, n = self.shape
                    return Matrix(tuple(tuple(self[i, j] for j in range(n)) for i in range(m)))
        else:
            args = self.args
        return self.func(*args, evaluate=True)

    @cacheit
    def _eval_shape(self):
        shape = ()
        for arg in self.args:
            _shape = arg.shape
            if len(_shape) > len(shape):
                shape = _shape
        return shape

    def _eval_is_even(self):
        odd = self.is_odd
        if odd is None:
            return odd
        return not odd

    def as_expr(self):
        return self

    @cacheit
    def _eval_domain_defined(self, x, **kwargs):
        if x.dtype.is_set:
            return x.universalSet
        domain = x.domain
        
        for arg in self.args:
            domain &= arg.domain_defined(x, **kwargs)
        return domain

    def _eval_is_extended_real(self):
        for arg in self.args:
            if arg.is_extended_real == False:
                return False
        return True

    _eval_is_super_real = lambda self: _fuzzy_group((a.is_super_real for a in self.args), quick_exit=True)
    _eval_is_extended_integer = lambda self: _fuzzy_group((a.is_extended_integer for a in self.args), quick_exit=True)
    
    def _eval_is_random(self):
        for arg in self.args:
            if arg.is_random:
                return True

    def getitem(self, indices, **_):
        if (indices := self.simplify_indices(indices)) is None:
            return self
        
        args = []
        len_shape = self.max_len_shape()
        if isinstance(indices, tuple):
            slice_length = sum(isinstance(i, Tuple) for i in indices)
            len_subtracted = len(indices) - slice_length
            is_slice = slice_length > 0
        elif isinstance(indices, Tuple):
            len_subtracted = 0
            is_slice = True
        else:
            len_subtracted = 1
            is_slice = False
            
        len_required = len_shape - len_subtracted
        for arg in self.args:
            shape_length = len(arg.shape)
            if shape_length < len_required:
                args.append(arg)
            elif shape_length == len_required:
                if is_slice:
                    if isinstance(indices, tuple):
                        args.append(arg[indices[len_shape - shape_length:]])
                    else:
                        args.append(arg[indices])
                else:
                    args.append(arg)
            elif isinstance(indices, tuple):
                args.append(arg[indices[len_shape - shape_length:]])
            else:
                args.append(arg[indices])

        return self.func(*args)

    @property
    def variables(self):
        s = set()
        for a in self.args:
            s |= {*a.variables}
            
        return s
    
    def yield_random_symbols(self):    
        for arg in self.args:
            yield from arg.yield_random_symbols()
        
    def yield_effective_variable(self, variable):
        for arg in self.args:
            yield from arg.yield_effective_variable(variable)

    def domain_definition(self, **_):
        from sympy import And
        return And(*(arg.domain_definition() for arg in self.args))

    def rotary_match(self, cls, indices):
        indices[:] = [None] * len(indices)
        if cls.of_LinearPattern():
            if self._coeff_isneg():
                return -self
            return

        from sympy.core.of import Basic
        if len(cls.args) == 2:
            from sympy.core.expr import Expr
            a, b = cls.args
            cls = Basic.__new__(self.func, b, a)
            args = Expr.of(self, cls, indices=indices)
            if args is not None:
                indices.reverse()
                if cls.of_LinearPattern():
                    if isinstance(args, tuple):
                        return self.func(*args)
                    return args

                if any(index is None for index in indices):
                    return args

                if isinstance(args, tuple):
                    if len(args) > 2:
                        if a is Expr:
                            _b, *_a = args
                            _a = self.func(*_a)
                        else:
                            *_b, _a = args
                            _b = self.func(*_b)
                    else:
                        _b, _a = args
                    return _a, _b
            return args
        
        for i, Ty in enumerate(cls.args):
            args = [*self.args]
            Ty_indices = [t for t, arg in enumerate(args) if isinstance(Ty, type) and isinstance(arg, Ty) or isinstance(Ty.func, type) and isinstance(arg, Ty.func)]
            if len(Ty_indices) == 1:
                types = [*cls.args]
                j, = Ty_indices
                del types[i]
                
                Ty_value = args.pop(j)
                Ty_value = Ty_value.of(Ty)
                if Ty_value is None:
                    break

                indices_ = [None] * len(types)
                args = self.func(*args).of(Basic.__new__(self.func, *types), indices=indices_)
                if args:
                    any_is_null = False
                    for t, index in enumerate(indices_):
                        if index is None:
                            any_is_null = True
                            continue

                        if t >= i:
                            index += 1
                            t += 1

                        indices[t] = index

                    if isinstance(args, tuple) and len(args) == len(cls.args) - 1:
                        if Ty_value:
                            return args[:i] + (Ty_value,) + args[i:]
                        return args
                    
                    if any_is_null:
                        if Ty_value == ():
                            if isinstance(Ty, type) and Ty.is_Symbol:
                                if all(index is None for index in indices[:i]):
                                    indices[i] = j
                                    if sum(index is not None for index in indices_) == 1:
                                        return self.args[j], args
                                    else:
                                        return self.args[j], *args
                                else:
                                    return
                            return args


class ShortCircuit(Exception):
    pass


class LatticeOp(AssocOp):
    """
    Join/meet operations of an algebraic lattice[1].

    Explanation
    ===========

    These binary operations are associative (op(op(a, b), c) = op(a, op(b, c))),
    commutative (op(a, b) = op(b, a)) and idempotent (op(a, a) = op(a) = a).
    Common examples are AND, OR, Union, Intersection, max or min. They have an
    identity element (op(identity, a) = a) and an absorbing element
    conventionally called zero (op(zero, a) = zero).

    This is an abstract base class, concrete derived classes must declare
    attributes zero and identity. All defining properties are then respected.

    Examples
    ========

    >>> from sympy import Integer
    >>> from sympy.core.operations import LatticeOp
    >>> class my_join(LatticeOp):
    ...     zero = Integer(0)
    ...     identity = Integer(1)
    >>> my_join(2, 3) == my_join(3, 2)
    True
    >>> my_join(2, my_join(3, 4)) == my_join(2, 3, 4)
    True
    >>> my_join(0, 1, 4, 2, 3, 4)
    0
    >>> my_join(1, 2)
    2

    References:

    .. [1] https://en.wikipedia.org/wiki/Lattice_%28order%29
    """

    is_commutative = True

    def as_two_terms(self):
        """Return head and tail of self.

        This is the most efficient way to get the head and tail of an
        expression.

        - if you want only the head, use self.args[0];
        - if you want to process the arguments of the tail then use
          self.as_coef_add() which gives the head and a tuple containing
          the arguments of the tail when treated as an Add.
        - if you want the coefficient when self is treated as a Mul
          then use self.as_coeff_mul()[0]

        >>> from sympy.abc import x, y
        >>> (3*x - 2*y + 5).as_two_terms()
        (5, 3*x - 2*y)
        """
        return self.args[0], self.func(*self.args[1:])

    def __new__(cls, *args, **options):
        args = [_sympify_(arg) for arg in args]

        try:
            # /!\ args is a generator and _new_args_filter
            # must be careful to handle as such; this
            # is done so short-circuiting can be done
            # without having to sympify all values
            if options.get('evaluate', True):
                args = frozenset(cls._new_args_filter(args))
            else:
                args = frozenset(args)
        except ShortCircuit:
            return sympify(cls.zero)
        if not args:
            return sympify(cls.identity)
        elif len(args) == 1:
            obj = set(args).pop()
            if obj.is_BooleanAtom:
                obj = obj.copy(**options)
            return obj
        else:
            # XXX in almost every other case for __new__, *_args is
            # passed along, but the expectation here is for _args
            obj = super(AssocOp, cls).__new__(cls, args, **options)
            obj._argset = args
            return cls.ensure_correctness_of_assumptions(obj, **options)

    @classmethod
    def ensure_correctness_of_assumptions(cls, obj, **options):
        if cls.is_Boolean:
            if 'equivalent' in options:
                if obj.equivalent is not options['equivalent']:
                    obj = obj.copy(**options)
            elif 'given' in options:
                if obj.given is not options['given']:
                    obj = obj.copy(**options)
            elif 'imply' in options:
                if obj.imply is not options['imply']:
                    obj = obj.copy(**options)
        return obj
        
    @classmethod
    def _new_args_filter(cls, arg_sequence, call_cls=None):
        """Generator filtering args"""
        ncls = call_cls or cls
        for arg in arg_sequence: 
            if ncls._need_to_be_raised(arg):
                raise ShortCircuit(arg)
            elif ncls._need_to_be_filtered(arg):
                continue
            elif arg.func == ncls:
                yield from arg.args
            else:
                yield arg

    @classmethod
    def make_args(cls, expr):
        """
        Return a set of args such that cls(*arg_set) == expr.
        """
        if isinstance(expr, cls):
            return expr._argset
        else:
            return frozenset([sympify(expr)])

    # XXX: This should be cached on the object rather than using cacheit
    # Maybe _argset can just be sorted in the constructor?
    @property  # type: ignore
    @cacheit
    def args(self):
        return tuple(sorted(self._argset, key=lambda x: x.sort_key()))

    @staticmethod
    def _compare_pretty(a, b):
        return (str(a) > str(b)) - (str(a) < str(b))

    def of(self, cls):
        res = AssocOp.of(self, cls)
        if res is None:
            if cls.is_LatticeOp:
                from sympy.core.of import Basic
                if isinstance(cls, Basic) or cls.is_IndexedOperator:
                    a, b = cls.args
                    cls = Basic.__new__(cls.func, b, a)
                    res = AssocOp.of(self, cls)
                    if isinstance(res, tuple):
                        b, a = res
                        return a, b
        return res

    @cacheit
    def sort_key(self, order=None):
        args = self._sorted_args
        args = len(args), tuple(arg.class_key() for arg in args), tuple(arg.sort_key(order=order) for arg in args)
        from sympy import S
        return self.class_key(), args, S.One.sort_key(), S.One


class AssocOpDispatcher:
    """
    Handler dispatcher for associative operators

    .. notes::
       This approach is experimental, and can be replaced or deleted in the future.
       See https://github.com/sympy/sympy/pull/19463.

    Explanation
    ===========

    If arguments of different types are passed, the classes which handle the operation for each type
    are collected. Then, a class which performs the operation is selected by recursive binary dispatching.
    Dispatching relation can be registered by ``register_handlerclass`` method.

    Priority registration is unordered. You cannot make ``A*B`` and ``B*A`` refer to
    different handler classes. All logic dealing with the order of arguments must be implemented
    in the handler class.

    Examples
    ========

    >>> from sympy import Add, Expr, Symbol
    >>> from sympy.core.add import add

    >>> class NewExpr(Expr):
    ...     @property
    ...     def _add_handler(self):
    ...         return NewAdd
    >>> class NewAdd(NewExpr, Add):
    ...     pass
    >>> add.register_handlerclass((Add, NewAdd), NewAdd)

    >>> a, b = Symbol('a'), NewExpr()
    >>> add(a, b) == NewAdd(a, b)
    True

    """

    def __init__(self, name, doc=None):
        self.name = name
        self.doc = doc
        self.handlerattr = "_%s_handler" % name
        self._handlergetter = attrgetter(self.handlerattr)
        self._dispatcher = Dispatcher(name)

    def __repr__(self):
        return "<dispatched %s>" % self.name

    def register_handlerclass(self, classes, typ, on_ambiguity=ambiguity_register_error_ignore_dup):
        """
        Register the handler class for two classes, in both straight and reversed order.

        Paramteters
        ===========

        classes : tuple of two types
            Classes who are compared with each other.

        typ:
            Class which is registered to represent *cls1* and *cls2*.
            Handler method of *self* must be implemented in this class.
        """
        if not len(classes) == 2:
            raise RuntimeError(
                "Only binary dispatch is supported, but got %s types: <%s>." % (
                len(classes), str_signature(classes)
            ))
        if len(set(classes)) == 1:
            raise RuntimeError(
                "Duplicate types <%s> cannot be dispatched." % str_signature(classes)
            )
        self._dispatcher.add(tuple(classes), typ, on_ambiguity=on_ambiguity)
        self._dispatcher.add(tuple(reversed(classes)), typ, on_ambiguity=on_ambiguity)

    @cacheit
    def __call__(self, *args, _sympify=True, **kwargs):
        """
        Parameters
        ==========

        *args :
            Arguments which are operated
        """
        if _sympify:
            args = tuple(map(_sympify_, args))
        handlers = frozenset(map(self._handlergetter, args))

        # no need to sympify again
        return self.dispatch(handlers)(*args, _sympify=False, **kwargs)

    @cacheit
    def dispatch(self, handlers):
        """
        Select the handler class, and return its handler method.
        """

        # Quick exit for the case where all handlers are same
        if len(handlers) == 1:
            h, = handlers
            if not isinstance(h, type):
                raise RuntimeError("Handler {!r} is not a type.".format(h))
            return h

        # Recursively select with registered binary priority
        for i, typ in enumerate(handlers):

            if not isinstance(typ, type):
                raise RuntimeError("Handler {!r} is not a type.".format(typ))

            if i == 0:
                handler = typ
            else:
                prev_handler = handler
                handler = self._dispatcher.dispatch(prev_handler, typ)

                if not isinstance(handler, type):
                    raise RuntimeError(
                        "Dispatcher for {!r} and {!r} must return a type, but got {!r}".format(
                        prev_handler, typ, handler
                    ))

        # return handler class
        return handler

    @property
    def __doc__(self):
        docs = [
            "Multiply dispatched associative operator: %s" % self.name,
            "Note that support for this is experimental, see the docs for :class:`AssocOpDispatcher` for details"
        ]

        if self.doc:
            docs.append(self.doc)

        s = "Registered handler classes\n"
        s += '=' * len(s)
        docs.append(s)

        amb_sigs = []

        typ_sigs = defaultdict(list)
        for sigs in self._dispatcher.ordering[::-1]:
            key = self._dispatcher.funcs[sigs]
            typ_sigs[key].append(sigs)

        for typ, sigs in typ_sigs.items():

            sigs_str = ', '.join('<%s>' % str_signature(sig) for sig in sigs)

            if isinstance(typ, RaiseNotImplementedError):
                amb_sigs.append(sigs_str)
                continue

            s = 'Inputs: %s\n' % sigs_str
            s += '-' * len(s) + '\n'
            s += typ.__name__
            docs.append(s)

        if amb_sigs:
            s = "Ambiguous handler classes\n"
            s += '=' * len(s)
            docs.append(s)

            s = '\n'.join(amb_sigs)
            docs.append(s)

        return '\n\n'.join(docs)
