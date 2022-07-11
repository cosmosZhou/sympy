
# 符号推理，机器证明的探索历程
  <br>
  
  
在2008年,
作者通过学习C++编程语言，开启一个浩繁、旷日持久的征途：公理化机械化数学证明工具，其目标就是设计一个能自动解决数学问题的机器，
辅助，甚至取代人脑进行复杂的数学推理。该项目主要是在作者的业余时间完成。当初，该工程最初由C++编写，
主要基于一个德国的开源符号计算项目[ginac](https://www.ginac.de/)，这是个C++数学符号算法库，
而此数学半机械化推导的算法是基于符号计算展开的。
当时作者也没有精力学习其它编程语言，限于有限的编程技能，只能首先尝试使用C/C++来写程序，
也是当时最流行的编程语言。
------
在2016年, 作者发现了其它许多不同编程编写的开源符号计算工程，比如[sympy](https://www.sympy.org/en/index.html), 及其C++子项目 [symengine](https://github.com/symengine/symengine.git)，还有一个Common-Lisp项目[Maxima](http://maxima.sourceforge.net)，一个集成各种符号计算的工具集项目[sagemath](https://www.sagemath.org/)，包含了Maxima, [Maple](https://www.maplesoft.com/products/Maple/),
Mathematica, [Matlab](https://www.mathworks.com/products/matlab.html), sympy; 以及一些自动化机器证明的资料： [theoremprover-museum](https://theoremprover-museum.github.io/),
[Proof_assistant](https://en.wikipedia.org/wiki/Proof_assistant), 
[Interactive_proof_system](https://en.wikipedia.org/wiki/Interactive_proof_system).


随着机器学习、人工智能技术的发展，Python成为算法领域最流行的编程语言，鉴于其高效的开发效率（开发效率远超C++,当然执行效率却不到C++的10%），
以及其普遍适用性（ Python从流行、普及程度上超过Common-Lisp语言），也是在语法上最接近数学语言的编程语言，从此，
作者开始转型Python算法。这个公理化的数学工具也逐渐改写（翻译）成Python语言。。 

--------
在2018年, 作者筹建了一个网站，也即[axiom.top](../axiom)。其目的在于分享这个公理化半机械化数学定理证明工具。
作者也希望通过开源社区的力量，逐渐壮大已知数学定理库的覆盖范围。
如果定理库足够大，利用海量的题库训练数据集，一个基于深度学习模型的自动解题机器有就可能在本世纪被制造出来。
当然这绝对不是一个人的脑力在有生之年可以完成的。

--------
在2021年, 一个基于transformer，公开的基于符号推理和神经网络的几何数学自动求解器被设计出来。  
项目说明文档地址为https://lupantech.github.io/inter-gps/  
代码位于：https://github.com/lupantech/InterGPS  
论文地址：https://arxiv.org/pdf/2105.04165.pdf  
中文资料：https://mp.weixin.qq.com/s/ZFpVpi7BsJME6uXi_2IcrQ  

这个研究为通用数学题的机器求解提供了很好的思路，就是：将数学问题用形式语言精确表达出来，构建一个庞大的训练数据集，然后用transformer训练一个序列转序列的神经网络，同时结合符号推理的算法，预测推算出需要调用定理的序列，从而实现通用数学命题的机器证明。  
当然也面临很多问题，比如其中的难题就是：通用数学命题的自动证明并不是一个单纯的已知定理序列的预测过程，因为每个定理在调用时，我们往往要对参数进行一定的调整，这不光是一个序列预测的问题。