from sympy.core import Basic

from sympy.strategies import typed, exhaust, condition, do_one, unpack
from sympy.strategies.traverse import bottom_up
from sympy.utilities import sift

from sympy.matrices.expressions.matexpr import MatrixExpr, ZeroMatrix, Identity
from sympy.matrices.expressions.matpow import MatPow
from sympy.matrices.expressions.transpose import Transpose, transpose

from sympy.matrices.expressions.inverse import Inverse
from sympy.matrices import Matrix, ShapeError
from sympy.core.logic import _fuzzy_group


class BlockMatrix(MatrixExpr): 
    """
    Represents a block matrix.
    Examples
    ========

    >>> n = Symbol.n(integer=True, positive=True)
    >>> A = Symbol.A(shape=(n, n), real=True)
    >>> B = Symbol.B(shape=(n, n), real=True)
    >>> C = Symbol.C(shape=(n, n), real=True)
    >>> D = Symbol.D(shape=(n, n), real=True)
    >>> block1 = BlockMatrix([[A, B], [C, D]])
    >>> block1
    [[A, B], [C, D]]
    >>> _A = Symbol("A'", shape=(n, n), real=True)
    >>> _B = Symbol("B'", shape=(n, n), real=True)
    >>> _C = Symbol("C'", shape=(n, n), real=True)
    >>> _D = Symbol("D'", shape=(n, n), real=True)
    >>> block2 = BlockMatrix([[_A, _C], [_B, _D]])
    >>> block2
    [[A, B], [C, D]]
    >>> discrete.matmul.to.blockMatrix.apply(block1 @ block2, deep=True)
    
    
    """

    @property
    def dtype(self):
        dtype = None
        for arg in self.args:
            _dtype = arg.dtype
            if dtype is None or dtype in _dtype:
                dtype = _dtype
        return dtype

    def __new__(cls, *args, **kwargs):
        if len(args) > 1 and isinstance(args[-1], tuple):
            *args, (axis,) = args
        elif 'axis' in kwargs:
            axis = kwargs.pop('axis')
        else:
            axis = 0
        _args = []
        
        if len(args) == 1 and isinstance(args[0], (list, tuple)):
            args = args[0]
            if all(isinstance(arg, (list, tuple)) for arg in args):
                args = [cls(*(x.T for x in arr)).T for arr in args]                
        
        from sympy import sympify
        args = [*map(sympify, args)]
        length = max(len(arg.shape) for arg in args)
        for arg in args: 
            if isinstance(arg, BlockMatrix) and len(arg.shape) == length and arg.axis == axis:
                _args += arg.args
            else:
                _args.append(arg)
        if all(not arg.shape for arg in _args):
            return Matrix(tuple(_args))
        blocks = Basic.__new__(cls, *_args, **kwargs)
        blocks.axis = sympify(axis)
        return blocks
    
    @property
    def kwargs(self):
        # return hyper parameter of this object
        return {'axis': self.axis}

    @staticmethod
    def broadcast(shapes):
        length = 0
        cols = 0
        for i, shape in enumerate(shapes):
            if not shape:
                shapes[i] = (1,)
                shape = shapes[i]
            if len(shape) > 2:
                ...
            else:
                if shape[-1] > cols:
                    cols = shape[-1]
            if len(shape) > length:
                length = len(shape)
                
        if length == 1 and all(shape[0] == shapes[0][0] and len(shape) == length for shape in shapes):            
            length += 1
            
        for i, shape in enumerate(shapes):
            if len(shape) > 2:
                ...
            else:
                if shape[-1] < cols and len(shape) > 1:
                    shape = shape[:-1] + (cols,)
            if len(shape) < length:
                shape = (1,) * (length - len(shape)) + shape
            shapes[i] = shape
        return shapes
    
    def _eval_shape(self):
        if self.axis:
            shapes = [arg.shape for arg in self.args]
            max_length = {len(s) for s in shapes}
            assert len(max_length) == 1
            max_length, *_ = max_length            
            assert self.axis < max_length
            
            for axis in {*range(max_length)} - {self.axis}:
                if len({s[axis] for s in shapes}) > 1:
                    print([s[axis] for s in shapes])
                assert len({s[axis] for s in shapes}) == 1

            shape = shapes[0]
            dimension_axis = 0
            for s in shapes:
                dimension_axis += s[self.axis]
            return shape[:self.axis] + (dimension_axis,) + shape[self.axis + 1:max_length]
        else:
            shapes = [arg.shape for arg in self.args]
            self.broadcast(shapes)
            rows = sum(s[0] for s in shapes)
            if len(shapes[0]) > 1:
                return (rows, *shapes[0][1:])
            else:
                return (rows,)
        
    @property
    def shape(self):
        if 'shape' in self._assumptions:
            return self._assumptions['shape']
        shape = self._eval_shape()
        self._assumptions['shape'] = shape
        return shape

    def __getitem__(self, key):
        from sympy.functions.elementary.piecewise import Piecewise
        if isinstance(key, slice):
            start, stop = key.start, key.stop
            if start is None:
                start = 0
            if stop is None:
                stop = self.shape[0]
                
            if start == 0 and stop == self.shape[0]:
                return self
            
            rows = 0
            args = []
            
            len_self_shape = len(self.shape)
            for arg in self.args:
                if start >= stop:
                    break
                index = rows
                if len(arg.shape) < len_self_shape:
                    rows += 1
                else:
                    rows += arg.shape[0]

                if start < rows:
                    if len(arg.shape) < len_self_shape:
                        args.append(arg)
                        start += 1
                    elif rows <= stop:
                        if rows - start < arg.shape[0]:
                            args.append(arg[start:])
                        else:
                            args.append(arg)
                        start = rows
                    else:
                        args.append(arg[start - index: stop - index])
                        start = stop
            if len(args) == 1:
                return args[0]
            if len(args) == 0:
                return ZeroMatrix(*self.shape)
            return self.func(*args)
        if isinstance(key, tuple):
            if len(key) == 1:
                key = key[0]
                
            elif len(key) == 2:
                i, j = key
                if isinstance(i, slice):
                    if isinstance(j, slice):
                        raise Exception('unimplemented method')
                    else:
                        assert i.step is None, 'unimplemented slice object %s' % i
                        start, stop = i.start, i.stop                        
                        if start is None:
                            if stop is None:
                                # v have the same columns
                                args = []
                                for v in self.args:
                                    if len(v.shape) > 1:
                                        indexed = v[:, j]
                                    else:
                                        indexed = v[j]
                                    args.append(indexed)
                                return self.func(*args)

                        raise Exception('unimplemented slice object %s' % i)
                elif isinstance(j, slice):
                    raise Exception('unimplemented method') 
                from sympy.core.sympify import _sympify
                i, j = _sympify(i), _sympify(j)
                if self.valid_index(i, j) != False: 
                    args = []
                    length = 0
                    for arg in self.args:
                        _length = length
                        
                        shape = arg.shape                         
                        length += shape[0]
                        cond = i < length
                        if len(arg.shape) == 1:
                            args.append([arg[j], cond])
                        else: 
                            if cond.is_BooleanFalse:
                                continue                         
                            args.append([arg[i - _length, j], cond])
                            
                    args[-1][-1] = True
                    return Piecewise(*args)
                else:
                    raise IndexError("Invalid indices (%s, %s)" % (i, j))
                
        if isinstance(key, int) or key.is_Integer or key.is_Symbol or key.is_Expr:
            if self.axis == 0: 
                from sympy import S
                rows = S.Zero
                args = []
                for arg in self.args:
                    index = rows
                    if len(arg.shape) < len(self.shape):
                        rows += S.One
                    else:
                        rows += arg.shape[0]
                        
                    cond = key < rows
                    if cond.is_BooleanFalse:
                        continue
                    
                    if len(arg.shape) < len(self.shape):
                        args.append([arg, cond])
                    else:
                        args.append([arg[key - index], cond]) 
                args[-1][-1] = True
                return Piecewise(*args)
            else:
                return self.func(*(a[key] for a in self.args), axis=self.axis - 1)                

        raise IndexError("Invalid index, wanted %s[i,j]" % self)

    def _eval_determinant(self):
        from sympy.concrete.products import Product
        if self.is_upper or self.is_lower:
            i = self.generate_var(integer=True)
            return Product(self[i, i], (i, 0, self.cols)).doit()

    @property
    def is_lower(self):
        """Check if matrix is a lower triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_lower
        True

        >>> m = Matrix(4, 3, [0, 0, 0, 2, 0, 0, 1, 4 , 0, 6, 6, 5])
        >>> m
        Matrix([
        [0, 0, 0],
        [2, 0, 0],
        [1, 4, 0],
        [6, 6, 5]])
        >>> m.is_lower
        True

        >>> from sympy.abc import x, y
        >>> m = Matrix(2, 2, [x**2 + y, y**2 + x, 0, x + y])
        >>> m
        Matrix([
        [x**2 + y, x + y**2],
        [       0,    x + y]])
        >>> m.is_lower
        False

        See Also
        ========

        is_upper
        is_diagonal
        is_lower_hessenberg
        """
        from sympy import Range, Min

        i = self.generate_var(domain=Range(0, Min(self.rows, self.cols - 1)))
        j = i.generate_var(free_symbols=self.free_symbols, domain=Range(i + 1, self.cols))
        assert i < j
        return self[i, j] == 0

    @property
    def is_upper(self):
        """Check if matrix is an upper triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_upper
        True

        >>> m = Matrix(4, 3, [5, 1, 9, 0, 4 , 6, 0, 0, 5, 0, 0, 0])
        >>> m
        Matrix([
        [5, 1, 9],
        [0, 4, 6],
        [0, 0, 5],
        [0, 0, 0]])
        >>> m.is_upper
        True

        >>> m = Matrix(2, 3, [4, 2, 5, 6, 1, 1])
        >>> m
        Matrix([
        [4, 2, 5],
        [6, 1, 1]])
        >>> m.is_upper
        False

        See Also
        ========

        is_lower
        is_diagonal
        is_upper_hessenberg
        """
        from sympy import Range, Min

        j = self.generate_var(domain=Range(0, Min(self.cols, self.rows - 1)))
        i = j.generate_var(free_symbols=self.free_symbols, domain=Range(j + 1, self.rows))
        assert i > j
        return self[i, j] == 0

    def __add__(self, other):
        if isinstance(other, BlockMatrix):
            if len(self.args) == len(other.args):
                if all(x.shape == y.shape for x, y in zip(self.args, other.args)):
                    return self.func(*[x + y for x, y in zip(self.args, other.args)])
        return MatrixExpr.__add__(self, other)

    def simplify(self, deep=False, **kwargs):
        if deep:
            return MatrixExpr.simplify(self, deep=deep, **kwargs)
        if self.axis == 0:
            if self.shape[0] == len(self.args):
                from sympy import Indexed
                start = None
                for i, arg in enumerate(self.args):
                    if not isinstance(arg, Indexed):
                        return self
                    diff = arg.indices[-1] - i
                    if start is None:
                        start = diff
                    else:
                        if start != diff:
                            return self
                    
                return arg.base[start:len(self.args)]
            
            b = None
            
            start, stop = None, None
            for arg in self.args:
                if arg.is_Slice or arg.is_Indexed:
                    if b is None:
                        b = arg.base
                    elif b != arg.base or len(arg.indices) > 1:
                        b = None
                        break
                                        
                    if start is None:
                        if arg.is_Slice:
                            start, stop = arg.index
                        else:
                            start = arg.index
                            stop = start + 1
                    else:
                        if arg.is_Slice: 
                            _start, _stop = arg.index
                        else:
                            _start = arg.index
                            _stop = _start + 1
                            
                        if _start != stop:
                            b = None
                            break
                        stop = _stop
            if b is not None:
                return b[start:stop]        
        return self
    
    @property
    def blocks(self):
        cols = None
        blocks = []
        for X in self.args: 
            if X.is_Transpose and X.arg.is_BlockMatrix:
                if cols is None:
                    cols = len(X.arg.args)
                else:
                    if cols != len(X.arg.args):
                        return
                blocks.append([x.T for x in X.arg.args])
                continue
            if len(X.shape) == 1 and X.is_BlockMatrix:
                if cols is None:
                    cols = len(X.args)
                else:
                    if cols != len(X.args):
                        return
                blocks.append([x for x in X.args])
                continue                
                
            return
        
        for i in range(cols):
            cols = None
            block = [block[i] for block in blocks]
            matrix = [b for b in block if len(b.shape) == 2]           
            
            if matrix:
                shape = matrix[0].shape
                if len(shape) == 2:
                    cols = shape[-1]
                else:
                    cols = shape[-1]
                    
                if any(m.shape[-1] != cols for m in matrix):
                    return
                
                vector = [b for b in block if len(b.shape) == 1]
                if any(v.shape[0] != cols for v in vector):
                    return
                
                scalar = [b for b in block if len(b.shape) == 0]
                if scalar:
                    return
                
        return blocks
        
    # {c} means center, {l} means left, {r} means right
    def _latex(self, p):
#         return r'\begin{pmatrix}%s\end{pmatrix}' % r'\\'.join('{%s}' % self._print(arg) for arg in expr.args)

        blocks = self.blocks
        if blocks is not None:
            cols = len(blocks[0])
            array = (' & '.join('{%s}' % p._print(X) for X in block) for block in blocks)
            return r"\left[\begin{array}{%s}%s\end{array}\right]" % ('c' * cols, r'\\'.join(array))
            
        array = []
        for X in self.args: 
            if X.is_Transpose and X.arg.is_BlockMatrix: 
                X = X.arg       
                latex = r"{\left[\begin{array}{%s}%s\end{array}\right]}" % ('c' * len(X.args),
                                                                            ' & '.join('{%s}' % p._print(arg.T) for arg in X.args))
            else:
                latex = '{%s}' % p._print(X)   
            array.append(latex)

        if len(self.shape) == 1 or self.axis:
            delimiter = ' & '
            center = 'c' * len(self.args)
        else:
            delimiter = r'\\'
            center = 'c'
            
        latex = r"\left[\begin{array}{%s}%s\end{array}\right]" % (center, delimiter.join(array))
        if self.axis:
            latex = "%s_%s" % (latex, p._print(self.axis))
        return latex
#         return r"\begin{equation}\left(\begin{array}{c}%s\end{array}\right)\end{equation}" % r'\\'.join('{%s}' % self._print(arg) for arg in expr.args)

    def _sympystr(self, p):
        tex = r"[%s]" % ','.join(p._print(arg) for arg in self.args)
        if self.axis:
            tex = '%s[%s]' % (tex, self.axis)
        return tex

    def _pretty(self, p): 
        return p._print_seq(self.args, '[', ']')
    
    def _eval_domain_defined(self, x, **_):
        if x.dtype.is_set:
            return x.universalSet
        
        domain = x.domain
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain

    def _eval_transpose(self):
        blocks = self.blocks
        if blocks is None:
            if len(self.shape) == 1:
                return self
            return
        rows = len(blocks)
        cols = len(blocks[0])
        
        blocks_T = [[None] * rows for _ in range(cols)]
        for i in range(rows):
            for j in range(cols):
                blocks_T[j][i] = blocks[i][j]
        return self.func(*[self.func(*block).T for block in blocks_T])

    def __rmul__(self, other): 
        if not other.shape:
            return self.func(*(other * arg for arg in self.args))
        return MatrixExpr.__rmul__(self, other)

    _eval_is_integer = lambda self: _fuzzy_group((a.is_integer for a in self.args), quick_exit=True)
    
    _eval_is_rational = lambda self: _fuzzy_group((a.is_rational for a in self.args), quick_exit=True)
    
    _eval_is_extended_real = lambda self: _fuzzy_group((a.is_extended_real for a in self.args), quick_exit=True)
    
    _eval_is_complex = lambda self: _fuzzy_group((a.is_complex for a in self.args), quick_exit=True)
    
    _eval_is_extended_positive = lambda self: _fuzzy_group((a.is_extended_positive for a in self.args), quick_exit=True)
    
    _eval_is_extended_negative = lambda self: _fuzzy_group((a.is_extended_negative for a in self.args), quick_exit=True)

    _eval_is_finite = lambda self: _fuzzy_group((a.is_finite for a in self.args), quick_exit=True)

        
class BlockDiagMatrix(MatrixExpr):
    """
    A BlockDiagMatrix is a BlockMatrix with matrices only along the diagonal

    >>> from sympy import MatrixSymbol, BlockDiagMatrix, symbols, Identity
    >>> n, m, l = symbols('n m l')
    >>> X = MatrixSymbol('X', n, n)
    >>> Y = MatrixSymbol('Y', m ,m)
    >>> BlockDiagMatrix(X, Y)
    Matrix([
    [X, 0],
    [0, Y]])

    See Also
    ========
    sympy.matrices.common.diag
    """

    def __new__(cls, *mats):
        return Basic.__new__(BlockDiagMatrix, *mats)

    @property
    def diag(self):
        return self.args

    @property
    def blocks(self):
        from sympy.matrices.immutable import ImmutableDenseMatrix
        mats = self.args
        data = [[mats[i] if i == j else ZeroMatrix(mats[i].rows, mats[j].cols)
                        for j in range(len(mats))]
                        for i in range(len(mats))]
        return ImmutableDenseMatrix(data)

    @property
    def shape(self):
        return (sum(block.rows for block in self.args),
                sum(block.cols for block in self.args))

    @property
    def blockshape(self):
        n = len(self.args)
        return (n, n)

    @property
    def rowblocksizes(self):
        return [block.rows for block in self.args]

    @property
    def colblocksizes(self):
        return [block.cols for block in self.args]

    def _eval_inverse(self, expand='ignored'):
        return BlockDiagMatrix(*[mat.inverse() for mat in self.args])

    def _blockmul(self, other):
        if (isinstance(other, BlockDiagMatrix) and
                self.colblocksizes == other.rowblocksizes):
            return BlockDiagMatrix(*[a * b for a, b in zip(self.args, other.args)])
        else:
            return BlockMatrix._blockmul(self, other)

    def _blockadd(self, other):
        if (isinstance(other, BlockDiagMatrix) and
                self.blockshape == other.blockshape and
                self.rowblocksizes == other.rowblocksizes and
                self.colblocksizes == other.colblocksizes):
            return BlockDiagMatrix(*[a + b for a, b in zip(self.args, other.args)])
        else:
            return BlockMatrix._blockadd(self, other)


def block_collapse(expr):
    """Evaluates a block matrix expression

    >>> from sympy import MatrixSymbol, BlockMatrix, symbols, \
                          Identity, Matrix, ZeroMatrix, block_collapse
    >>> n,m,l = symbols('n m l')
    >>> X = MatrixSymbol('X', n, n)
    >>> Y = MatrixSymbol('Y', m ,m)
    >>> Z = MatrixSymbol('Z', n, m)
    >>> B = BlockMatrix([[X, Z], [ZeroMatrix(m, n), Y]])
    >>> print(B)
    Matrix([
    [X, Z],
    [0, Y]])

    >>> C = BlockMatrix([[Identity(n), Z]])
    >>> print(C)
    Matrix([[I, Z]])

    >>> print(block_collapse(C*B))
    Matrix([[X, Z + Z*Y]])
    """
    from sympy.matrices.expressions.matmul import MatMul
    hasbm = lambda expr: isinstance(expr, MatrixExpr) and expr.has(BlockMatrix)
    rule = exhaust(
        bottom_up(exhaust(condition(hasbm, typed(
            {MatAdd: do_one(bc_matadd, bc_block_plus_ident),
             MatMul: do_one(bc_matmul, bc_dist),
             MatPow: bc_matmul,
             Transpose: bc_transpose,
             Inverse: bc_inverse,
             BlockMatrix: do_one(bc_unpack, deblock)})))))
    result = rule(expr)
    doit = getattr(result, 'doit', None)
    if doit is not None:
        return doit()
    else:
        return result


def bc_unpack(expr):
    if expr.blockshape == (1, 1):
        return expr.blocks[0, 0]
    return expr


def bc_matadd(expr):
    args = sift(expr.args, lambda M: isinstance(M, BlockMatrix))
    blocks = args[True]
    if not blocks:
        return expr

    nonblocks = args[False]
    block = blocks[0]
    for b in blocks[1:]:
        block = block._blockadd(b)
    if nonblocks:
        return MatAdd(*nonblocks) + block
    else:
        return block


def bc_block_plus_ident(expr):
    idents = [arg for arg in expr.args if arg.is_Identity]
    if not idents:
        return expr

    blocks = [arg for arg in expr.args if isinstance(arg, BlockMatrix)]
    if (blocks and all(b.structurally_equal(blocks[0]) for b in blocks)
               and blocks[0].is_structurally_symmetric):
        block_id = BlockDiagMatrix(*[Identity(k)
                                        for k in blocks[0].rowblocksizes])
        return MatAdd(block_id * len(idents), *blocks).doit()

    return expr


def bc_dist(expr):
    """ Turn  a*[X, Y] into [a*X, a*Y] """
    factor, mat = expr.as_coeff_mmul()
    if factor != 1 and isinstance(unpack(mat), BlockMatrix):
        B = unpack(mat).blocks
        return BlockMatrix([[factor * B[i, j] for j in range(B.cols)]
                                              for i in range(B.rows)])
    return expr


def bc_matmul(expr):
    if isinstance(expr, MatPow):
        if expr.args[1].is_Integer:
            factor, matrices = (1, [expr.args[0]] * expr.args[1])
        else:
            return expr
    else:
        factor, matrices = expr.as_coeff_matrices()

    i = 0
    while (i + 1 < len(matrices)):
        A, B = matrices[i:i + 2]
        if isinstance(A, BlockMatrix) and isinstance(B, BlockMatrix):
            matrices[i] = A._blockmul(B)
            matrices.pop(i + 1)
        elif isinstance(A, BlockMatrix):
            matrices[i] = A._blockmul(BlockMatrix([[B]]))
            matrices.pop(i + 1)
        elif isinstance(B, BlockMatrix):
            matrices[i] = BlockMatrix([[A]])._blockmul(B)
            matrices.pop(i + 1)
        else:
            i += 1
    from sympy.matrices.expressions.matmul import MatMul
    return MatMul(factor, *matrices).doit()


def bc_transpose(expr):
    return BlockMatrix(block_collapse(expr.arg).blocks.applyfunc(transpose).T)


def bc_inverse(expr):
    expr2 = blockinverse_1x1(expr)
    if expr != expr2:
        return expr2
    return blockinverse_2x2(Inverse(reblock_2x2(expr.arg)))


def blockinverse_1x1(expr):
    if isinstance(expr.arg, BlockMatrix) and expr.arg.blockshape == (1, 1):
        mat = Matrix([[expr.arg.blocks[0].inverse()]])
        return BlockMatrix(mat)
    return expr


def blockinverse_2x2(expr):
    if isinstance(expr.arg, BlockMatrix) and expr.arg.blockshape == (2, 2):
        # Cite: The Matrix Cookbook Section 9.1.3
        [[A, B],
         [C, D]] = expr.arg.blocks.tolist()

        return BlockMatrix([[ (A - B * D.I * C).I, (-A).I * B * (D - C * A.I * B).I],
                            [-(D - C * A.I * B).I * C * A.I, (D - C * A.I * B).I]])
    else:
        return expr


def deblock(B):
    """ Flatten a BlockMatrix of BlockMatrices """
    if not isinstance(B, BlockMatrix) or not B.blocks.has(BlockMatrix):
        return B
    wrap = lambda x: x if isinstance(x, BlockMatrix) else BlockMatrix([[x]])
    bb = B.blocks.applyfunc(wrap)  # everything is a block

    from sympy import Matrix
    try:
        MM = Matrix(0, sum(bb[0, i].blocks.shape[1] for i in range(bb.shape[1])), [])
        for row in range(0, bb.shape[0]):
            M = Matrix(bb[row, 0].blocks)
            for col in range(1, bb.shape[1]):
                M = M.row_join(bb[row, col].blocks)
            MM = MM.col_join(M)

        return BlockMatrix(MM)
    except ShapeError:
        return B


def reblock_2x2(B):
    """ Reblock a BlockMatrix so that it has 2x2 blocks of block matrices """
    if not isinstance(B, BlockMatrix) or not all(d > 2 for d in B.blocks.shape):
        return B

    BM = BlockMatrix  # for brevity's sake
    return BM([[   B.blocks[0, 0], BM(B.blocks[0, 1:])],
               [BM(B.blocks[1:, 0]), BM(B.blocks[1:, 1:])]])


def bounds(sizes):
    """ Convert sequence of numbers into pairs of low-high pairs

    >>> from sympy.matrices.expressions.blockmatrix import bounds
    >>> bounds((1, 10, 50))
    [(0, 1), (1, 11), (11, 61)]
    """
    low = 0
    rv = []
    for size in sizes:
        rv.append((low, low + size))
        low += size
    return rv


def blockcut(expr, rowsizes, colsizes):
    """ Cut a matrix expression into Blocks

    >>> from sympy import ImmutableMatrix, blockcut
    >>> M = ImmutableMatrix(4, 4, range(16))
    >>> B = blockcut(M, (1, 3), (1, 3))
    >>> type(B).__name__
    'BlockMatrix'
    >>> ImmutableMatrix(B.blocks[0, 1])
    Matrix([[1, 2, 3]])
    """

    rowbounds = bounds(rowsizes)
    colbounds = bounds(colsizes)
    from sympy.matrices.expressions.slice import MatrixSlice
    return BlockMatrix([[MatrixSlice(expr, rowbound, colbound)
                         for colbound in colbounds]
                         for rowbound in rowbounds])

# from sympy.core.sympify import converter
# converter[list] = lambda l: BlockMatrix(l)
