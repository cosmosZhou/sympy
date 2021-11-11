# 什么是axiom.top  
  <br>

[axiom.top](../axiom.php)是一个基于数学定理知识库、用于证明数学命题的网站，此工程主要依靠开源符号计算项目 
[sympy](https://github.com/sympy/sympy) 和 
[Maxima](http://maxima.sourceforge.net) 改写, 其中函数命名主要参考数学软件语言
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer)
。 其主要特征在于：半机械化、公理化、追求逻辑严密性。目前该工具可以应用于求证数学课本上的证明题。
	
	
* 所述半机械化，是指目前做不到全自动根据数学命题题设直接打印出证明过程，而是需要人脑的辅助，人必须通过检索定理库，告诉计算机，面对什么样的题型使用什么样的定理；
* 所述公理化，是指所有数学定理，归根结底可以用公理来解释，而公理是不需要证明的，其真伪是人为假定成立的，整个数学定理库就是建立在公理的假设之上展开构建的；
* 所述追求逻辑严密性，就是依据[希尔伯特纲领](https://en.wikipedia.org/wiki/Hilbert%27s_program)中的申明，在论证过程中，以[形式语言](https://en.wikipedia.org/wiki/Formal_language)的既定逻辑来引导程序进行推理，力求确保计算结果在[形式语言](https://en.wikipedia.org/wiki/Formal_language)的既定语法规则内有效，且所有推理都依据某个公理或者定理进行。在本系统中，所有数学问题都将被[Python](https://www.python.org/)语句精确描述出来，不存在自然语言描述数学问题时存在的歧义性。

该系统的三个基本元素是[Symbol](../axiom.php?symbol=Symbol), [Function](../axiom.php?symbol=Function), Theorem；
* Symbol是一个字母或者数字组合的变量。变量命名规则与[Python](https://www.python.org/)一致。用于定义任意类型的抽象数学符号，比如  
n = Symbol(integer=True, positive=True, random=True)表示一个正整数随机变量,   
p, q = Symbol(prime=True)表示p是一个素数, q也是一个素数；   
m = Symbol(integer=True, nonnegative=True)表示一个非负整数,   
t = Symbol(domain=Range(0, m))表示t是一个整数，取值范围是[0; m)；   
a = Symbol(integer=True, shape=(oo,))表示一个无限大的整数向量，  
b = Symbol(hyper_real=True, shape=(oo, oo))表示一个无限大的hyper real矩阵，  
c = Symbol(complex=True, shape=(n, n, n))表示一个n * n * n的复数张量，  
A = Symbol(etype=dtype.real, measurable=True)，表示一个[可测](https://en.wikipedia.org/wiki/Measure_(mathematics))实数集合，etype意思为element type;  
B = Symbol(etype=dtype.real, countable=True)，表示一个[可数](https://en.wikipedia.org/wiki/Countable_set)实数集合;  
C = Symbol(etype=dtype.integer, shape=(n,))，表示一个整数集合的列表，该列表有n个元素；  
Q = Symbol(etype=dtype.rational.set)，表示一个集合，它的元素是一个有理数集合。
* Function表示对其它符号或者函数的某种运算；  
f, f1 = Function(hyper_real=True)，表示f, f1都是抽象hyper real函数。  
g = Function(real=True, eval=lambda x: x \* x)，表示一个实数函数, 定义为g(x) = x<sup>2</sup>。  
h = Function(etype=dtype.integer)，表示一个返回值是一个整数集合的抽象函数。  
f = Function(real=True, continuous=True)，表示一个实数抽象（在任意点）连续函数。  
f = Function(real=True, differentiable=True)，表示一个实数抽象（在任意点）可微函数。  
f = Function(measurable=True, domain=Interval(0, 1))，表示一个可测实数抽象函数，值域为[0, 1]。  
f = Function(real=True, integrable=True)，表示一个实数抽象（在任意区间内）Lebesgue可积函数。  
以及系统内置函数，比如[cos](../axiom.php?symbol=cos)(x), [sin](../axiom.php?symbol=sin)(x), [tan](../axiom.php?symbol=tan)(x), [log](../axiom.php?symbol=log)(x), [exp](../axiom.php?symbol=exp)(x), 以及大型运算符[Sum](../axiom.php?symbol=Sum)\[k:a:b\](h\[k\]), [Product](../axiom.php?symbol=Product)\[k:a:b\](h\[k\]), [All](../axiom.php?symbol=All)\[k:a:b\](h\[k\] > t\[k\]), [Any](../axiom.php?symbol=Any)\[k:a:b\](h\[k\] > t\[k\])等等，所有函数都不会进行浮点数运算，因为在定理推导系统中，没有浮点数的概念，一切都是严格意义上的数学符号与函数。  
* Theorem表示一个定理或者公理；    
Theorem的入参是一个表达式，出参是一个判断表达式。它以定理库的形式储存。基本用法就是Theorem.apply(...);  
比如  
a, b, c = Symbol(complex=True)  
[algebra.poly_is_zero.imply.et.suffice.cubic.apply](../axiom.php?module=algebra.poly_is_zero.imply.et.suffice.cubic)(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x),  表示对一个一元三次方程在复数域内求解。  
比较Mathematica的方程解：
https://www.wolframcloud.com/obj/744984949/Published/cubic_root.  

其中数集的关系定义为：  
[prime](https://en.wikipedia.org/wiki/Prime_number) ⊂ [natural](https://en.wikipedia.org/wiki/Natural_number) ⊂ [integer](https://en.wikipedia.org/wiki/Integer) ⊂ extended_integer  
[rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ extended_rational  
[real](https://en.wikipedia.org/wiki/Real_number) ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [super_real](https://en.wikipedia.org/wiki/Superreal_number)  
[complex](https://en.wikipedia.org/wiki/Complex_number) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)  
[integer](https://en.wikipedia.org/wiki/Integer) ⊂ [rational](https://en.wikipedia.org/wiki/Rational_number) ⊂ [real](https://en.wikipedia.org/wiki/Real_number) ⊂ [complex](https://en.wikipedia.org/wiki/Complex_number)  
extended_integer ⊂ extended_rational ⊂ [extended_real](https://en.wikipedia.org/wiki/Extended_real_number_line) ⊂ [extended_complex](https://en.wikipedia.org/wiki/Riemann_sphere)  
[hyper_real](https://en.wikipedia.org/wiki/Hyperreal_number) ⊂ [hyper_complex](https://en.wikipedia.org/wiki/Hypercomplex_number)  
[super_real](https://en.wikipedia.org/wiki/Superreal_number) ⊂ [super_complex](https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers)  

<br><br>
------


# 数学定理库的建设
  <br>
  
目前积累了<label id=count>____</label>个已知数学定理用于半机械化数学推导。主要涉及：	
	
* [algebra](../axiom.php?module=algebra) 初等代数，主要涉及等式的恒等、换元变换、有限级数[∑裂项求和](../axiom.php?module=algebra.sum.to.add.telescope)、∏裂项求积技巧，不等式的传递性质的命题，[一元一次方程](../axiom.php?module=algebra.poly_is_zero.imply.et.suffice.simple_equation)，[一元二次方程](../axiom.php?module=algebra.poly_is_zero.imply.et.suffice.quadratic)，[一元三次方程](../axiom.php?module=algebra.poly_is_zero.imply.et.suffice.cubic)，[一元四次方程](../axiom.php?module=algebra.poly_is_zero.imply.et.suffice.quartic)的求解问题，初等函数的各种常见性质；
[数学归纳法](../axiom.php?module=algebra.ne_zero.suffice.imply.is_nonzero.induct)的证明；
* [sets](../axiom.php?module=sets) 集合论, 即sets theory，集合论是整个数学分析、数学推导系统的理论核心；涉及大量用集合论术语ForAll（任意）, Exists（存在）, ‘属于’ （Element），‘包含’（Subset）描述的命题，比如
[容斥原理](../axiom.php?module=sets/imply/eq/principle/inclusion_exclusion/basic)的证明。可以说，集合论是数学推理的根本语法。
* [geometry](../axiom.php?module=geometry) 几何学，主要分为初中
[平面几何学](../axiom.php?module=geometry/plane)，(中学三角函数学) 与高中
[立体几何学](../axiom.php?module=geometry/solid)； 包含不少三角函数恒等式，比如
[和差化积](../axiom.php?module=geometry.cos.to.add.principle.add)，[积化和差](../axiom.php?module=geometry.mul.to.add.sin)，等等。
* [calculus](../axiom.php?module=calculus) 微积分，主要包含以下内容： 
[极限定义](../axiom.php?module=calculus/eq/to/any_all/limit_definition) 及其理论，它是微积分的理论基础； 
[无穷级数](../axiom.php?module=calculus.eq.imply.eq.series.infinite.coefficient) 的运算性质；
[分部积分](../axiom.php?module=calculus.integral.to.add.by_parts) 定理；
三角函数及其它少数超越函数的积分；
* [discrete](../axiom.php?module=discrete) 数论，离散数学，组合数学，线性代数，包含一些基本的排列组合的计算公式的证明（比如
[排列数](../axiom.php?module=discrete.abs_cup.to.factorial) 的组合学计算，组合数的组合学计算， [第二类Stirling数](../axiom.php?module=discrete.stirling2.to.add.recurrence) 的组合学推导， 
[Catalan数](../axiom.php?module=discrete.eq.eq.imply.eq.catalan.recurrence) 的推导）， 
[连分数](../axiom.php?module=discrete.add.to.pow.HK.recurrence) 初步理论；以及与矩阵的行列式相关的若干命题。
* [stats](../axiom.php?module=stats) 概率统计学，主要包含常见概率分布（比如二项式分布，正态分布，poisson分布，die分布，Χ<sup>2</sup>分布）相关公式的推导，以及[Bayes公式](../axiom.php?module=stats/probability/to/mul)相关的命题；
* [keras](../axiom.php?module=keras) 机器学习，深度学习中的数学模型，主要包括用于研究自然语言的数学模型，
[GRU](https://arxiv.org/abs/1412.3555v1)，
[LSTM](https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015)，
[BERT](https://arxiv.org/abs/1706.03762)，
[TEXT-CNN](https://arxiv.org/pdf/1408.5882.pdf)，
条件自由场[CRF](https://arxiv.org/abs/1603.01360) 模型的计算公式以其在计算上的各种性质，以及KMeans
[聚类收敛性](../axiom.php?module=sets.el.notin.le.imply.le.st.variance) 部分证明。概率论为机器学习提供了理论上的依据。  
* 今后不久将增加物理，化学，生物方面（及其分支学科）的数学应用，以记录数学方法在实用科技方面的经典成功应用，从而推动应用科学技术发展的历史。

<br><br>
-------
该公理化半机械化数学证明工具可以简化论证过程，实现“给思考加上发动机”，研究者只需掌握论证的宏观脉络，具体计算交付给计算机即可。主要可以用于理论性数学证明，对数学学院的学生，算法工程师、研究员在算法研究，数学分析过程中有一定参考价值，
也可以用于数学工作者整理数学定理知识，无需手动编辑繁琐的数学公式，无需手动进行纸笔演算，通过在线的[Python](https://www.python.org/)集成开发环境IDE,就可以对定理过程进行编辑，从而完成数学定理的整理工作。其中在线IDE提供F3快捷键可以方便定位任意定理，函数，符号的定义，
对于研究和教学都有化繁为简的实用价值，是一本电子版的数学定理、算法模型参考书。
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script	src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>

<script>
	$('#count').load("/sympy/php/request/count.php");
</script>