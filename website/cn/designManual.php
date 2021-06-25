<h1>设计文档</h1>
<h2>主要设计理念</h2>
<p>计算机本身并不会根据论据推导出新的论点，也不像人一样会使用自然语言进行推理，它并不会思考，只会作数值与符号计算
	（当然如果我们把思考定义为逻辑计算，那么计算机也能思考，并且速度远超人类），
	所以如果能设计一种算法把抽象推理问题转化成一个计算问题，那么计算机也可以进行抽象推理。
	理性思辨能力不一定需要自然语言的辅助。只不过我们习惯使用自然语言来思考问题。
	在不使用自然语言的前提下，想证明排列组合教科书上的几个基本的结论也会变得异常复杂。
	不过作者找到了使用集合论作为理论基础的一般证明方法，证明了组合学教材中使用自然语言进行论证的例题。
	事实上，严格的数学证明就不能使用自然语言来论证，使用自然语言证明的数学命题，看起来很直观易懂，其实很值得怀疑。
	在公理化推导系统中，一切命题都是似是而非的，除非你能把这个命题分解成有限个公理来推导，那么这个命题就是真命题。
	否则就只是个猜想，这也是公理化数学推导系统的基本原则。</p>
<br>
<hr />
<h2>软件主要功能</h2>
<br>
<p>
	该软件的主要目的是：为数学专业师生及爱好者，算法研究员设计一个能摆脱重复、繁琐纸笔演算的公理化、半机械化数学证明工具。<br>
	主要功能在于三方面：
<ul>
	<li>1，提供了一个公理化的数学定理库，覆盖集合论，数论，代数，离散数学，组合学，几何学，三角学，微积分，概率论，深度学习等几个分支学科。
	
	
	<li>2，提供了一个人机互动的机器证明算法，用户需引导机器调用已知定理，引导机器步步求解，机器自动打印证明过程，为用户节省了繁琐的纸笔演算时间。
	
	
	<li>3，提供了一个可视化数学定理图形用户界面，包括关键词检索功能以及刻画定理之间依存关系的层级图，方便用户阅读相关数学定理。

</ul>

<br>
主要技术特点：
<ul>
	<li>1，建立了一套以公理为证明依据的公理化论证系统。
	
	<li>2，建立了一套基于定理库的、人机互动的、半机械化机器论证方法。
	
	<li>3，使用前端技术将定理的检索及定理引用关系可视化。

</ul>

根据数学定理的题设（given）和结论（imply），计算机，在人脑通过检索定理知识库，提供正确的预备已知定理的前提下，不断调用已知定理得到变换后的条件表达式，并不断逼近最终结论（imply）表达式，从而获得命题的证明。
数学证明过程（prove）就是将题设（given）表达式不断变换成结论（imply）表达式的过程，
这个证明过程（prove）由一系列已知定理调用命令和符号计算结果组成，一个已知定理调用命令对应一个符号计算结果。 命题证毕后使用
<a href="https://www.latex-project.org/">latex</a>
，
<a href="https://www.mathjax.org/">mathjax.js</a>
，
<a href="https://vuejs.org/index.html/">vue.js</a>
，
<a href="https://www.php.net">php</a>
等前端可视化技术打印出数学命题证明的全过程，方便日后参考学习。
</p>
<hr />
<h2>算法实现原理</h2>
此公理化定理推导工具工作原理如下：
<li>1，首先制定一套公理化的数学推导理论，将所有数学命题使用严格的数学语法用公理，定理，运算法则推导出来，在推导过程中不使用自然语言的辅助；</li>
<li>2，实现一个半机械化的推导系统。每个数学证明题由三部分组成：题设（given），结论（imply），证明过程（prove）；
	计算机的工作就是给出这个数学证明题的完整证明过程。如果计算机在证明过程（prove）中,能根据题设（given）提供的信息，使用已知数学定理库中的知识（具体使用哪个定理由人脑决策给出），
	对题设（given）中的条件表达式进行各种变换（比如恒等式变换，换元变换，不等式放缩变换，这个涉及数学技巧），
	最终得出结论（imply）完全一致的条件表达式，则表明计算机完成了给定数学命题的证明过程。</li>
<li>3，人脑通过对已知定理库进行知识检索，在推导过程中发挥了数学定理选择决定权，也就是告知计算机面对什么样数学命题使用什么样的已知定理进行下一步推理，计算机根据人输入的Python命令利用符号计算算法和既定的逻辑推导法则进行推理，得出一个更接近结论（imply）的表达式，并最终得出结论（imply），从而使数学命题获得证明。</li>

<div id=content></div>

