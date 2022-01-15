from util import *


def is_one_hot(row):
    index = None
    for j, cell in enumerate(row):
        if cell.is_Identity:
            if index is not None:
                return
            index = j
            continue
        if not cell.is_ZeroMatrix:
            return
    return index


def swap_col(blocks, i, j):
    if i < j:
        start = i + 1
        stop = j
    elif i > j:
        start = j + 1
        stop = i
    else:
        return 0

    for row in blocks:
        row[i], row[j] = row[j], row[i]

    x = blocks[0][i].shape[-1]
    y = blocks[0][j].shape[-1]

    return x * y + sum([blocks[0][k].shape[-1] for k in range(start, stop)]) * (x + y)


@apply
def apply(self):
    X = self.of(Det)
    blocks = [[*b] for b in X.blocks]
    permutation = [is_one_hot(row) for row in blocks]

    s = 0
    for i in range(len(permutation)):
        j = permutation[i]
        s += swap_col(blocks, i, j)
        permutation[i], permutation[j] = permutation[j], permutation[i]

    return Equal(self, (-1) ** s)


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    Eq << apply(Det(BlockMatrix([
        [ZeroMatrix(n, m), Identity(n), ZeroMatrix(n, m)],
        [Identity(m), ZeroMatrix(m, n), ZeroMatrix(m, m)],
        [ZeroMatrix(m, m), ZeroMatrix(m, n), Identity(m)]])))


if __name__ == '__main__':
    run()
# created on 2021-11-21
