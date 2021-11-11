from util.search import read_all_py
from run import project_directory

from util.cpp import instance as lib, vector
from ctypes import c_char_p, c_void_p
from _ctypes import Structure


class CodeBlock(Structure):
    _fields_ = [("ptr", c_void_p)]
    
    def __del__(self):
        lib.delete_CodeBlock(self)

    
lib.compile[c_char_p] = vector(CodeBlock)
lib.delete_CodeBlock[CodeBlock] = None

if __name__ == '__main__':
    for py in read_all_py(project_directory()):
        print(py)
        with open(py, 'r') as file:
            text = file.read()
            print(text)
            break
        
