import json
import os


def cstring(s):
    return bytes(s, 'utf8')


def is_Windows():
    return os.sep == '\\'

    
# is Linux System
def is_Linux():
    return os.sep == '/'


def json_encode(data, utf8=False): 
    s = json.dumps(data, ensure_ascii=False)
    if utf8:
        s = s.encode(encoding='utf-8')
    return s 


def eol_convert(fileName):
    with open(fileName, "rb") as f:
        data = bytearray(os.path.getsize(fileName))
        f.readinto(data)
        # print(data)
        data = data.replace(b"\r\n", b"\n")

    with open(fileName, "wb") as f:
        # print(data)
        f.write(data)    


def HeapPermutation(k, A):
    '''
    https://en.wikipedia.org/wiki/Heap%27s_algorithm
    '''
    
    if k == 1:
        yield A
    else:
        # Generate permutations with kth unaltered, Initially k == length(A)
        yield from HeapPermutation(k - 1, A)
        
        # Generate permutations for kth swapped with each k-1 initial
        for i in range(k - 1):
            # Swap choice dependent on parity of k (even or odd)
            if k & 1:
                A[0], A[k - 1] = A[k - 1], A[0]
            else:
                A[i], A[k - 1] = A[k - 1], A[i]
            
            yield from HeapPermutation(k - 1, A)


def generate_all_permutation(A):
    yield from HeapPermutation(len(A), A)        

        
def skip_first_permutation(A):
    generator = HeapPermutation(len(A), A)
    next(generator)
    yield from generator


import heapq


class TopKHeap(object):

    def __init__(self, k):
        self.data = []
        self.k = k

    def push(self, num):

        if len(self.data) < self.k:
            heapq.heappush(self.data, num)
        elif num > self.data[0]:
                heapq.heapreplace(self.data, num)

    def topk(self):
        
        arr = []
        while self.data: 
            a = heapq.heappop(self.data)
            arr.append(a)
            
        arr.reverse()
        return arr



def argmax(arr):
    maxi = arr[0]
    index = 0
    for i in range(1, len(arr)):
        a = arr[i]
        if a > maxi:
            index = i
        
    return index

def argmin(arr):
    maxi = arr[0]
    index = 0
    for i in range(1, len(arr)):
        a = arr[i]
        if a < maxi:
            index = i
        
    return index

if __name__ == '__main__':
    import random
    heap = TopKHeap(10)
    for i in range(100):
        n = random.randint(0, 100)
        # print(n,'------------')
        heap.push(n)
    print(heap.topk())
    
