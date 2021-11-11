# What is axiom.top
  <br>
  
[axiom.top](../axiom.php) is a website for symbolic	semi-mechanized axiomatized theorem-proving system, the [github project](https://github.com/cosmosZhou/sympy) of which is based on open-source symbolic computation project of [sympy](https://github.com/sympy/sympy) and 
[Maxima](http://maxima.sourceforge.net), its main terminology is defined according to the naming conventions of the commercial algebraic system 
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). It's main ideals are: semi-mechanization, axiomatization, and the pursuit of logic correctness. At present, it can be used in conducting semi-automatic proving for theorems from mathematics textbook.  

* the above-mentioned semi-mechanization is so defined that:   
at present, we can't devise a fully-automatic machine to process human-like logic reasoning steps in theorem-proving according the given prerequisites and conclusions.  
The machine can only solve the mathematical problem according the instruction provided by humans. Humans must tell the computer by searching through the axiom knowledge bank, what theorems or axioms to apply in front of a given mathematical problem. 
* the above-mentioned axiomatization is so defined that:  
every mathematical theorem, in the final analysis, can be proved by axioms which are unprovable, which are assumed self-evident, whose correctness is hypothesized by humans to hold true.  
The whole mathematical theorem knowledge bank is built step by step on these presumably true hypotheses.

* the above-mentioned pursuit of logic correctness is so defined that:  
during the processing of conducting reasoning, in accordance with the statements defined in 
[Hilbert's program](https://en.wikipedia.org/wiki/Hilbert%27s_program), the program strives to be logically valid within the grammars defined by [formal language](https://en.wikipedia.org/wiki/Formal_language).   
Each theorem is proved according to the assumptions and correctness of some previously proved theorems or axioms. In this project, each mathematical problem will be expressed as a [Python](https://www.python.org/) statement which is precisely defined with no ambiguity which can emerge when one use natural language to express a mathematical problem.  


This system is comprised of three basic elements: [Symbol](../axiom.php?symbol=Symbol), [Function](../axiom.php?symbol=Function), Theorem; 
* Symbol is an identifier composed of a series of alphabets and digits. Its naming convention is the same as that of [Python](https://www.python.org/) programming language.   
It is used to define any abstract mathematical symbol or variable, for instance:     
n = Symbol(integer=True, positive=True, random=True, odd=True), denotes an odd positive random variable,  
p, q = Symbol(prime=True, even=False) denotes that p is an odd prime number, so is q;     
m = Symbol(integer=True, nonnegative=True) denotes a non-negative integer,   
t = Symbol(domain=Range(0, m)) denotes an integer ranging from 0 (including) to m (excluding);  
a = Symbol(integer=True, shape=(oo,)) denotes an infinitely large vector of integers;   
b = Symbol(real=True, shape=(oo, oo)) denotes an infinitely large matrix of reals;   
c = Symbol(complex=True, shape=(n, n, n)) denotes a complex tensor of shape n * n * n;   
A = Symbol(etype=dtype.real, measurable=True) denotes a [measurable](https://en.wikipedia.org/wiki/Measure_(mathematics)) set of reals, wherein etype is abbreviated from "element type";  
B = Symbol(etype=dtype.real, countable=True) denotes a [countable](https://en.wikipedia.org/wiki/Countable_set) set of reals;  
C = Symbol(etype=dtype.integer, shape=(n,)) denotes a vector of n sets of integers;     
Q = Symbol(etype=dtype.rational.set) denotes a set, the element of which is a set of rationals;    

* Function denotes a certain mathematical computations on other symbols or functions; for instance:  
f, f1 = Function(real=True) denotes that f, f1 are all abstract real function whose definition is unknown yet;   
g = Function(real=True, eval=lambda x: x \* x) denotes a real-valued function defined as: g(x) = x<sup>2</sup>;     
h = Function(etype=dtype.integer) denotes an abstract function whose return value is of type: integer set;  
f = Function(real=True, continuous=True) denotes a real-valued function continuous at any given point;    
f = Function(real=True, differentiable=True) denotes a real-valued function differentiable at any given point;    
f = Function(measurable=True, domain=Interval(0, 1)) denotes a measurable real-valued function whose value lies within domain [0, 1];    
f = Function(real=True, integrable=True) denotes a real-valued function Lebesgue-integrable at any given interval;    
as well as system built-in function, such as [cos](../axiom.php?symbol=cos)(x), [sin](../axiom.php?symbol=sin)(x), [tan](../axiom.php?symbol=tan)(x), [log](../axiom.php?symbol=log)(x), [exp](../axiom.php?symbol=exp)(x), and some more complex operators [Sum](../axiom.php?symbol=Sum)\[k:a:b\](h\[k\]), [Product](../axiom.php?symbol=Product)\[k:a:b\](h\[k\]), [ForAll](../axiom.php?symbol=All)\[k:a:b\](h\[k\] > t\[k\]), [Exists](../axiom.php?symbol=Any)\[k:a:b\](h\[k\] > t\[k\]), etc.  
All these functions will not perform any float-point calculations as usual, since during the process of mathematical proving, any involvement of calculations with float-point values will yield a logic error in pure mathematics.    
Every value in mathematical proving is in strict sense mathematical value, there is no concept of approximate values like float-pointing values;      


* Theorem denotes a theorem that is provable or an axiom that is unprovable ;      
The inputs of theorems must be expression(s) or condition(s), its outputs are necessarily condition(s). It is stored in a mysql database as a theorem knowledge bank. Its main usage is as follows: Theorem.apply(...); for instance:    
a, b, c = Symbol(complex=True)  
[algebra.poly_is_zero.imply.et.infer.cubic.apply](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.cubic)(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x), denotes the determination process of a cubic equation within the domain of Complexes.     

The number system set is defined as  
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


# The construction of Mathematical Theorem Repertoire
  <br>
  
As of this writing, <label id=count>____</label> theorems have been recored in the theorem repertoire, which can be applied in semi-mechanized axiomatized system of mathematical theorem proving.  
It is mainly comprising of :  	
	
* [algebra](../axiom.php?module=algebra) refers to elementary algebra, which mainly delves into equations transformation、symbol substitution techniques, finite series [∑ telescoping](../axiom.php?module=algebra.sum.to.add.telescope)、∏ product telescoping, the property of transitivity for inequalities, solving [simple equations](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.simple_equation), [quadratic equations](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.quadratic), [cubic equations](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.cubic) and [quartic equations](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.quartic), common properties of some elementary functions, as well as the proof of [mathematical induction method](../axiom.php?module=algebra.ne_zero.infer.imply.ne_zero.induct);   
* [sets](../axiom.php?module=sets) refers to sets theory, which is the core foundation of the theories of whole mathematical proving and analysis. It involves lots of propositions using the terminologies like 
ForAll, Exists, Element, Subset, for example: 
the proof of [inclusion-exclusion principle](../axiom.php?module=sets/imply/eq/principle/inclusion_exclusion/basic). It can be so said that: set theory is the fundamental grammar of automatic theorem proving.  
* [geometry](../axiom.php?module=geometry) is comprised of junior-middle school 
[plane geometry](../axiom.php?module=geometry/plane), trigonometry and senior-middle school
[solid geometry](../axiom.php?module=geometry/solid), some trigonometric identities, for instance:  
[addition principle of cosine](../axiom.php?module=geometry.cos.to.add.principle.add), [product principle of trigonometry](../axiom.php?module=geometry.mul.to.add.sin), and so on.   
* [calculus](../axiom.php?module=calculus) comprises :   
[the definition of limit](../axiom.php?module=calculus/eq/to/any_all/limit_definition) and its fundamental theories which is the theoretical basis of calculus.  
operational properties of [infinite series](../axiom.php?module=calculus.eq.imply.eq.series.infinite.coefficient); 
proof of [integration by parts](../axiom.php?module=calculus.integral.to.add.by_parts);  
determination of some integral for certain transcendental functions;  
* [discrete](../axiom.php?module=discrete) section is comprised of number theory, discrete mathematics, combinatorics, linear algebra, some basic counting techniques involving permutations(such as 
[permutations](../axiom.php?module=discrete.abs_cup.to.factorial), combinatoric induction for [second Stirling Number](../axiom.php?module=discrete.stirling2.to.add.recurrence),  
derivation for [Catalan Number](../axiom.php?module=discrete.eq.eq.imply.eq.catalan.recurrence)， 
basics of [continued fraction](../axiom.php?module=discrete.add.to.pow.HK.recurrence); as well as propositons of determinant of matrix.  
* [stats](../axiom.php?module=stats) refers to statistics and probability theory, comprising: the derivation of the probability density formula of some common distribution (such as, binomial distribution, Gaussian distribution, poisson distribution, die distribution, Χ<sup>2</sup>distribution)，as well as propositions related to [Bayes theorem](../axiom.php?module=stats/probability/to/mul);  
* [keras](../axiom.php?module=keras) section is related to the mathematical theories behind the contemporary deep learning / machine learning techniques, including the mathematical modeling used in natural language processing / understanding, like the forward inference or backward propagation formula of 
[LSTM](https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015),
[BERT](https://arxiv.org/abs/1706.03762),
[TEXT-CNN](https://arxiv.org/pdf/1408.5882.pdf),
Conditional Random Field [CRF](https://arxiv.org/abs/1603.01360), 
and partial proof of KMeans
[clustering convergence](../axiom.php?module=sets.el.notin.le.imply.le.st.variance). Probability theory provides the fundamental theoretical basis for machine learning so that this contemporary technique can be  explainable.  
* In the near future sections for physics, chemistry, biology and their sub-divisions will be established to reveal the development of scientific discoveries that were successful due to application of mathematical analysis.  
<br><br>
-------
This newly emerged semi-mechanized axiomatized theorem-proving system can simplify reasoning steps in mathematical analysis, thus achieving the ideal of "plugging in the dynamos of thinking". The researcher need only master the macro skeleton of reasoning, leaving the detailed computation to computer. It can be applied for theoretical mathematical proving, which can be useful in providing reference or guidance during the course of mathematical analysis for algorithm engineers, researcher in their research work. It can also be used for mathematical researchers to manage and edit their theoretical papers, without the need of manual editing of mathematical formulae since the latex printing is automatically generated by programming. One Can even use the on-line Integrated Development Environment (IDE) for [Python](https://www.python.org/) to edit the mathematical theorems to finish theoretical research work. The on-line [Python](https://www.python.org/) IDE provides a powerful hotkey F3 for users to locate the definition of any symbol or function instantly. It is of practical use for theoretical research, industrial research or pedagogical purposes. It is an on-line reference book for both mathematical theorems and algorithmic models for industry.
<br><br>


<script	src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>

<script>
	$('#count').load("/sympy/php/request/count.php");
</script>