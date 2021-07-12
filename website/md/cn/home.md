# 什么是axiom.top  
  <br>

[axiom.top](../axiom.php)是一个基于数学定理知识库、用于证明数学命题的网站，此工程主要依靠开源符号计算项目 
[sympy](https://github.com/sympy/sympy) 和 
[Maxima](http://maxima.sourceforge.net) 改写, 其中部分代码由商业性数学软件语言
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer)
写成。 其主要特征在于：半机械化、公理化、底层算法基于符号计算。
	
	
* 所谓半机械化，是指目前做不到全自动根据数学命题题设直接打印出证明过程，而是需要人脑的辅助，人必须告诉计算机，面对什么样的题型使用什么样的定理；
* 所谓公理化，是指所有数学定理，归根结底可以用公理来解释，而公理是不需要证明的，其真伪是人为假定成立的，整个数学定理库就是建立在公理的假设之上展开构建的；
* 所谓基于符号计算，就是在论证过程中，把命题的推导最终表示成一个符号计算问题，从而把抽象、复杂的理性思辨机器化。  
<br><br>
------

# 数学定理库的建设
  <br>
  
目前积累了<label id=count>____</label>个已知数学定理用于半机械化数学推导。主要涉及：	
	
* [algebra](../axiom.php/algebra) 初等代数，主要涉及等式的恒等、换元变换、有限级数∑裂项求和、∏裂项求积技巧，不等式的传递性质的命题，一元低次方程的求解问题，初等函数的各种常见性质；
[数学归纳法](../axiom.php/algebra/is_nonzero/suffice/imply/is_nonzero/induct)的证明；
* [sets](../axiom.php/sets) 集合论, 即sets theory，集合论是整个数学分析、数学推导系统的理论核心；涉及大量用集合论术语All, Any, ‘属于’ （Contains），‘包含’（Subset）描述的命题，比如
[容斥原理](../axiom.php/sets/imply/eq/principle/inclusion_exclusion/basic)的证明。可以说，集合论是数学推理的根本语法。
* [geometry](../axiom.php/geometry) 几何学，主要分为初中
[平面几何学](../axiom.php/geometry/plane)，(中学三角函数学) 与高中
[立体几何学](../axiom.php/geometry/solid)； 包含不少三角函数恒等式，比如
[和差化积](../axiom.php/geometry/plane/trigonometry/cosine/principle/add)，积化和差，等等。
* [calculus](../axiom.php/calculus/) 微积分，主要包含以下内容： 
[极限定义](../axiom.php/calculus/eq/to/any_all/limit_definition) 及其理论，它是微积分的理论基础； 
[无穷级数](../axiom.php/calculus/series/infinite) 的运算性质；
[分部积分](../axiom.php/calculus/integral/by_parts) 定理；
三角函数及其它少数超越函数的积分；
* [discrete](../axiom.php/discrete/) 数论，离散数学，组合数学，线性代数，包含一些基本的排列组合的计算公式的证明（比如
[排列数](../axiom.php/discrete/combinatorics/permutation/factorial/definition) 的组合学计算，组合数的组合学计算， [第二类Stirling数](../axiom.php/discrete/combinatorics/stirling/second/recurrence) 的组合学推导， 
[Catalan数](../axiom.php/discrete/combinatorics/catalan/recurrence) 的推导）， 
[连分数](../axiom.php/discrete/continued_fraction/HK/recurrence) 初步理论；以及与矩阵的行列式相关的若干命题。
* [stats](../axiom.php/stats/) 概率统计学，主要包含常见概率分布（比如二项式分布，正态分布，poisson分布，die分布，Χ<sup>2</sup>分布）相关公式的推导，以及[Bayes公式](../axiom.php/stats/probability/to/mul)相关的命题；
* [keras](../axiom.php/keras/) 机器学习，深度学习中的数学模型，主要包括用于研究自然语言的数学模型，
[GRU](https://arxiv.org/abs/1412.3555v1)，
[LSTM](https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015)，
[BERT](https://arxiv.org/abs/1706.03762)，
[TEXT-CNN](https://arxiv.org/pdf/1408.5882.pdf)，
条件自由场[CRF](https://arxiv.org/abs/1603.01360) 模型的计算公式以其在计算上的各种性质，以及KMeans++
[聚类收敛性](../axiom.php/keras/cluster/KMeans/monotony) 部分证明。概率论为机器学习的数学提供了理论上的依据。
<br><br>
-------
该公理化半机械化数学证明工具主要可以用于理论性数学证明，对数学学院的学生，算法工程师、研究员在算法研究，数学分析过程中有一定参考价值，
也可以用于数学教师整理数学定理知识，无需手动编辑繁琐的数学公式，无需手动进行纸笔演算就可以完成数学定理的整理工作。
对于研究和教学都有化繁为简的实用价值，是一本电子版的数学定理、算法模型参考书。
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script	src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>

<script>
	$('#count').load("/sympy/php/request/count.php");
</script>