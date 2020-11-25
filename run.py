# coding=utf-8

import sys
# to run this script, please install:
# pip install mpmath==1.1.0
# pip install oauthlib
from axiom import prove
import os

def listdir(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

#         if path.endswith(sufix):
#             yield path
        if os.path.isdir(path):
            yield from listdir_recursive(path, sufix)


def listdir_recursive(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif os.path.isdir(path):
            yield from listdir_recursive(path, sufix)

def clean():    
    for php in listdir(os.path.abspath(os.path.dirname(__file__)) + '/axiom'):
        py = php.replace('.php', '.py')
        if not os.path.exists(py):
            print(php)
            os.remove(php)
    
def args_kwargs(argv):
    args = []
    kwargs = {}
    for arg in argv:
        arr = arg.split('=')
        if len(arr) == 2:
            key, value = arr
            kwargs[key] = value
        else:
            args.append(arg)
    return args, kwargs

if __name__ == '__main__':
    args, kwargs = args_kwargs(sys.argv[1:])
    if kwargs:
        if 'clean' in kwargs:
            clean()

    if not args:         
        prove.prove()
    else:            
        unproven = []

        erroneous = []

        websites = []

        import axiom  # @UnusedImport
        def generator():
            for package in args:
                package = package.replace('/', '.').replace('\\', '.')
                package = eval(package)
                ret = package.prove(package.__file__)
                yield package.__file__, ret
                
        prove.post_process(generator())
#         print('prove.print_summary()')
        prove.print_summary()
#     cd D:/Program Files/Wolfram Research/Mathematica/12.1/SystemFiles/Components/WolframClientForPython
#     pip install .

# export WOLFRAM_INSTALLATION_DIRECTORY=D:\Program Files\Wolfram Research\Mathematica\12.1
# https://reference.wolfram.com/language/WolframClientForPython/
# https://reference.wolfram.com/workbench/index.jsp
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/
# https://www.wolfram.com/language/fast-introduction-for-programmers/en/procedures/
# https://www.wolfram.com/language/fast-introduction-for-math-students/en/
# https://www.wolfram.com/language/elementary-introduction/2nd-ed/preface.html
# https://mathworld.wolfram.com/
# https://reference.wolfram.com/language/JLink/tutorial/WritingJavaProgramsThatUseTheWolframLanguage.html

# https://store.wolfram.com/arrive.cgi?URI=/catalog/
# https://www.wolfram.com/mathematica/pricing/home-hobby/

# https://www.ginac.de/ginac.git/
# git clone git://www.ginac.de/ginac.git
# https://sourceforge.net/projects/maxima/
# http://www.mmrc.iss.ac.cn/

# http://dandelion-ecl.sourceforge.net/update/
# http://mirrors.aliyun.com/gnu/emacs/windows/emacs-27/
# http://www.gnu.org/software/emacs/download.html

# https://doc.sagemath.org/html/en/reference/index.html
# https://doc.sagemath.org/html/en/reference/libs/sage/libs/ecl.html

# http://www.gigamonkeys.com/book/
# https://common-lisp.net/downloads

# python run.py axiom.sets.contains.imply.equality.union axiom.sets.contains.imply.subset