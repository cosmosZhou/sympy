<div id="body">
	<h1>什么是axiom.top?</h1>
	<br>
	<p>
		<a href="../axiom">axiom.top</a>
		是一个基于数学定理知识库、用于证明数学命题的网站，此工程主要依靠开源符号计算项目 <a
			href="https://github.com/sympy/sympy"> sympy </a> 和<a
			href="http://maxima.sourceforge.net"> Maxima </a>改写, 其中部分代码由商业性数学软件语言<a
			href="https://reference.wolfram.com/language/index.html.en?source=footer">
			Mathematica</a>写成。 其主要特征在于：半机械化、公理化、底层算法基于符号计算。
	
	
	<li>所谓半机械化，是指目前做不到全自动根据数学命题题设直接打印出证明过程，而是需要人脑的辅助，人必须告诉计算机，面对什么样的题型使用什么样的定理；</li>
	<li>所谓公理化，是指所有数学定理，归根结底可以用公理来解释，而公理是不需要证明的，其真伪是人为假定成立的，
		整个数学定理库就是建立在公理的假设之上展开构建的；</li>
	<li>所谓基于符号计算，就是在论证过程中，把命题的推导最终表示成一个符号计算问题，从而把抽象、复杂的理性思辨机器化。</li>
	</p>
	<br>
	<hr />
	<h1>数学定理库的建设</h1>
	<br>
	<p>
		<br>目前积累了<label id=count>____</label>个已知数学定理用于半机械化数学推导。主要涉及
	
	
	<li><a href="../axiom/algebre/">algebre</a>
		初等代数，主要涉及等式的恒等、换元变换、有限级数∑裂项求和、∏裂项求积技巧，不等式的传递性质的命题，一元低次方程的求解问题，初等函数的各种常见性质；
		<a
		href="../axiom/algebre/is_nonzero/sufficient/imply/is_nonzero/induction.php">数学归纳法</a>
		的证明；</li>
	<li><a href="../axiom/sets/">sets</a> 集合论, 即sets
		theory，集合论是整个数学分析、数学推导系统的理论核心；涉及大量用集合论术语‘任意’（ForAll）,
		‘存在’（Exists），‘属于’ （contains），‘包含’（subset）描述的命题，比如<a
		href="../axiom/sets/imply/eq/principle/inclusion_exclusion/basic.php">容斥原理</a>的证明。可以说，集合论是数学推理的根本语法。</li>
	<li><a href="../axiom/geometry/">geometry</a>几何学，主要分为初中<a
		href="../axiom/geometry/plane">平面几何学，中学三角函数学</a>与高中<a
		href="../axiom/geometry/solid">立体几何学</a>； 包含不少三角函数恒等式，比如<a
		href="../axiom/geometry/plane/trigonometry/cosine/principle/add.php">和差化积</a>，积化和差，等等。</li>
	<li><a href="../axiom/calculus/">calculus</a>微积分，主要包含以下内容： <a
		href="../axiom/calculus/eq/astype/exists/limit_definition.php">极限定义</a>
		及其理论，它是微积分的理论基础； <a href="../axiom/calculus/series/infinite/">无穷级数</a>的运算性质；
		<a href="../axiom/calculus/integral/by_parts.php">分部积分</a>定理；
		三角函数及其它少数超越函数的积分；</li>
	<li><a href="../axiom/discrete/">discrete</a>数论，离散数学，组合数学，线性代数，包含一些基本的排列组合的计算公式的证明（比如
		<a
		href="../axiom/discrete/combinatorics/permutation/factorial/definition.php">排列数</a>
		的组合学计算，组合数的组合学计算， <a
		href=../axiom/discrete/combinatorics/stirling/second/recurrence/general.php>第二类Stirling数</a>
		的组合学推导， <a
		href="../axiom/discrete/combinatorics/catalan/recurrence.php">Catalan数</a>
		的推导），证明过程使用集合论的语言来论证；以及与矩阵的行列式相关的若干命题。</li>
	<li><a href="../axiom/statistics/">statistics</a>概率统计学，主要包含常见概率分布（比如二项式分布，正态分布，poisson分布，die分布，Χ<sup>2</sup>分布）相关公式的推导，以及Bayes公式相关的命题；
		因作者没有找到Bayes定理的证明，把<a href="../axiom/statistics/bayes/theorem.php">Bayes公式</a>暂时设定为不可证明的公理。</li>
	<li><a href="../axiom/keras/">keras</a>机器学习，深度学习中的数学模型，主要包括用于研究自然语言的数学模型，
		<a href="https://arxiv.org/abs/1412.3555v1">GRU</a>，<a
		href="https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015">LSTM</a>，<a
		href="https://arxiv.org/abs/1706.03762">BERT</a>，<a
		href="https://arxiv.org/pdf/1408.5882.pdf">TEXT-CNN</a>，条件自由场（<a
		href="https://arxiv.org/abs/1603.01360">CRF</a>）模型的计算公式以其在计算上的各种性质。概率论为机器学习的数学提供了理论上的依据。</li>
	<br>

	该公理化半机械化数学证明工具主要可以用于理论性数学证明，对数学学院的学生，算法工程师、研究员在算法研究，数学分析过程中有一定参考价值，也可以用于数学教师整理数学定理知识，无需手动编辑繁琐的数学公式，无需手动进行纸笔演算就可以完成数学定理的整理工作。
	对于研究和教学都有化繁为简的实用价值，是一本电子版的数学定理、算法模型参考书。

	</p>
	<br>
</div>

<div style="margin: 10px auto; height: 16px; -ms-zoom: 1;">
	<small> <span><img align="absmiddle" src="png/national_emblem.png"><a
			href=http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937>浙公网安备33060202000937号</a></span>&nbsp;&nbsp;&nbsp;&nbsp;<a
		href=http://beian.miit.gov.cn>浙ICP备20017509号-3</a>
	</small>
</div>

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="../axiom/utility.js"></script>

<script>
	var count = document.querySelector('#count');
	console.log('count = ' + count.textContent);

	var request_url = "/sympy/axiom/request.php";
	
	request_post(request_url, {query: 'count'}).done(res => {
		console.log('res = ' + res);
		count.textContent = res;
	});
	
</script>