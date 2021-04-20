# SymPy

the latex is printed with the aid of the following project:

https://github.com/mathjax/MathJax.git

to avoid php websites to show .py files, add the following codes to 
D:\wamp64\bin\apache\apache2.4.39\conf\httpd.conf
or for higher version of apache
D:\wamp64\bin\apache\apache2.4.46\conf\httpd.conf
for windows.

<Files ~ "\.py|\.gitignore">
Order allow,deny
Deny from all
</Files>

<Directory ~ "__pycache__">
Order allow,deny
Deny from all
</Directory>


     cd D:/Program Files/Wolfram Research/Mathematica/12.1/SystemFiles/Components/WolframClientForPython
     pip install .

 export WOLFRAM_INSTALLATION_DIRECTORY=D:\Program Files\Wolfram Research\Mathematica\12.1
 https://reference.wolfram.com/language/WolframClientForPython/
 https://reference.wolfram.com/workbench/index.jsp
 https://www.wolfram.com/language/fast-introduction-for-programmers/en/
 https://www.wolfram.com/language/fast-introduction-for-programmers/en/procedures/
 https://www.wolfram.com/language/fast-introduction-for-math-students/en/
 https://www.wolfram.com/language/elementary-introduction/2nd-ed/preface.html
 https://mathworld.wolfram.com/
 https://reference.wolfram.com/language/JLink/tutorial/WritingJavaProgramsThatUseTheWolframLanguage.html

 https://store.wolfram.com/arrive.cgi?URI=/catalog/
 https://www.wolfram.com/mathematica/pricing/home-hobby/

 https://www.ginac.de/ginac.git/
 git clone git://www.ginac.de/ginac.git
 https://sourceforge.net/projects/maxima/
 http://www.mmrc.iss.ac.cn/

 http://dandelion-ecl.sourceforge.net/update/
 http://mirrors.aliyun.com/gnu/emacs/windows/emacs-27/
 http://www.gnu.org/software/emacs/download.html

 https://doc.sagemath.org/html/en/reference/index.html
 https://doc.sagemath.org/html/en/reference/libs/sage/libs/ecl.html

 http://www.gigamonkeys.com/book/
 https://common-lisp.net/downloads

 
# git clone https://github.com/sympy/sympy.git 