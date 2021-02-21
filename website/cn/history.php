<div id="body">
	<h1>axiom.top的缓慢发展简史</h1>
	<p>
		在2008年,
		软件作者通过学习C++编程语言，开始构思了他浩繁的项目：公理化机械化数学证明工具，其目标就是设计一个能自动解决数学问题的机器，
		辅助，甚至取代人脑进行复杂的数学推理。该项目主要是在作者的业余时间完成。当时，作者也只是一个大二学生。该工程最初由C++编写，
		主要基于一个德国的开源符号计算项目<a href="https://www.ginac.de/"> ginac</a>，这是个C++数学符号算法库，
		而此数学半机械化推导的算法是基于符号计算展开的。
		当时作者也没有精力学习其它编程语言，限于有限的编程技能，只能首先尝试使用C/C++来写程序，这也是绝大多数大学教授的编程语言，
		也是当时最流行的编程语言。
	</p>
	<br>
	<p>
		在2016年, 作者发现了其它许多不同编程编写的开源符号计算工程，比如<a
			href="https://www.sympy.org/en/index.html"> sympy</a>, 及其C++子项目 <a
			href="https://github.com/symengine/symengine.git"> symengine</a>，还有一个Common-Lisp项目<a
			href="http://maxima.sourceforge.net"> Maxima </a>，一个集成各种符号计算的工具集项目<a
			href="https://www.sagemath.org/"> sagemath</a>，包含了Maxima, <a
			href="https://www.maplesoft.com/products/Maple/"> Maple</a>,
		Mathematica, <a href="https://www.mathworks.com/products/matlab.html">
			Matlab</a>,
		以及sympy。随着机器学习、人工智能技术的发展，Python成为算法领域最流行的编程语言，鉴于其高效的开发效率（开发效率远超C++,当然执行效率却不到C++的10%），
		以及其普遍适用性（ Python从流行、普及程度上超过Common-Lisp语言），也是在语法上最接近数学语言的编程语言，从此，
		作者开始转型Python算法。这个公理化的数学工具也逐渐改写（翻译）成Python语言。。 <br>
	</p>
	<br>
	<p>
		在2018年, 作者筹建了一个网站，也即<a href="../axiom"> axiom.top</a>。其目的在于分享这个公理化半机械化数学定理证明工具。
		作者也希望通过开源社区的力量，逐渐壮大已知数学定理库的覆盖范围。
		如果定理库足够大，利用海量的题库训练数据集，一个基于深度学习模型的自动解题机器有就可能在本世纪被制造出来。
		当然这绝对不是一个人的脑力在有生之年可以完成的。
	</p>

</div>
