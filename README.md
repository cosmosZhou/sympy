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

*斜体*
**粗体**
# 一级标题
## 二级标题
###  三级标题
#### 四级标题
##### 五级标题
###### 六级标题

[sympy](https://github.com/sympy/sympy.git )

![图片名称](http://url/a.png)
> 引用

* 无序列表

1. 有序列表
2. 有序列表

---

3. 有序列表


`内联代码` 的使用

```
大段代码块
```


***这是斜体加粗的文字***

----

~~这是加删除线的文字~~

居中格式

>这是引用的内容
>>这是引用的内容
>>>>>>>>>>这是引用的内容

![blockchain](https://ss0.bdstatic.com/70cFvHSh_Q1YnxGkpoWK1HF6hhy/it/u=702257389,1274025419&fm=27&gp=0.jpg "区块链")

[简书](http://jianshu.com)

[百度](http://baidu.com)


- 列表内容
+ 列表内容
* 列表内容

上一级和下一级之间敲三个空格即可

1. 一级无序列表内容
    * 二级无序列表内容   
    * 二级无序列表内容   
    * 二级无序列表内容
   
2. 一级无序列表内容
    1. 二级有序列表内容   
    2. 二级有序列表内容   
    3. 二级有序列表内容
   
3. 一级有序列表内容
    * 二级无序列表内容   
    * 二级无序列表内容   
    * 二级无序列表内容
   
4. 一级有序列表内容
    1. 二级有序列表内容   
    2. 二级有序列表内容   
    3. 二级有序列表内容


姓名|技能|排行
---|:--:|---:
刘备|哭|大哥
关羽|打|二哥
张飞|骂|三弟


`create database hero;`

(```)
    function fun(){
         echo "这是一句非常牛逼的代码";
    }
    fun();
(```)


```flow
st=>start: 开始
op=>operation: My Operation
cond=>condition: Yes or No?
e=>end
st->op->cond
cond(yes)->e
cond(no)->op
&```
