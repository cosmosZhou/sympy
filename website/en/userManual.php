<h1>User Manual for Axiomatized/Semi-mechanized library of Theorems</h1>
<hr />
<h2>Online User Manual</h2>
<br>
<h3>Theorem Search Function</h3>
<p>
	Start the theorem library in the website<a href='../axiom/'>sympy/axiom</a>,
	or the theorem library search page<a href='../axiom/search'>sympy/axiom/search</a>,
	as follows:
</p>
<img class=zoom src="png/search/panel.png" alt="search box" />
<hr />
<br>
<p>input a keyword at the search box pointed by the red arrow, the
	keyword should represent a partial indicate of the full theorem name
	you want to search, for example, the keyword 'binomial' in 'binomial
	theorem', as follows:</p>
<img class=zoom src="png/search/keyword.png" alt="search keyword">
<hr />
<br>
<p>press Enter key, then we can view all the theorems that include the
	keyword 'binomial', as follows:</p>
<img class=zoom src="png/search/results.png" alt="搜索关键词" />
<hr />
<br>
<p>
	click the hyperlink pointed by the red arrow, we can view the whole
	proof process of <a
		href='../axiom/discrete/combinatorics/binomial/theorem.php'>binomial
		theorem</a>, we can also directly visit the get api: <a
		href='../axiom/search.php?keyword=binomial'>www.axiom.top/sympy/axiom/search.php?keyword=binomial</a>
	to acquire the search results. Both the graphical user interface and
	get api support<a
		href='http://www.regular-expressions.info/tutorial.html'>regular
		expression</a>, and whole word matching, e.g., <a
		href='../axiom/search.php?keyword=discrete.*binomial&regularExpression=true'>www.axiom.top/sympy/axiom/search.php?keyword=discrete.*binomial&amp;regularExpression=true</a>
	which indicates searching theorems that include both 'discrete' and
	'binomial'.
</p>
<hr />
<br>
<h3>Theorem Dependency Analysis</h3>
<br>
<h4>Dependency Graph of Callee Theorems</h4>
Take
<a href='../axiom/discrete/combinatorics/binomial/theorem.php'>Newton's
	Binomial Theorem</a>
as an example :
<br>
use the mouse to hover over the first hyperlink on the page, we shall
see the hint "callee hierarchy", as follows:
<img class=zoom src="png/hierarchy/hyperlink.png" />
<hr />
<br>
click the hyperlink, we enter the
<a
	href='../axiom/hierarchy.php?callee=axiom.discrete.combinatorics.binomial.theorem'>Dependency
	Graph of Callee Theorems</a>
, as follows:

<img class=zoom src="png/hierarchy/callee.png" />
<br>
the graph aboved shows the following theorems that employed 'binomial
theorem' in their process of proof:
<ul>
	<li><a href='../axiom/discrete/difference/factorial'>axiom.discrete.difference.factorial</a></li>
	<li><a href='../axiom/discrete/matrix/vandermonde/concatenate'>axiom.discrete.matrix.vandermonde.concatenate</a></li>
</ul>
in "Dependency Graph of Callee Theorems", click >>>>(expansion button),
we can further view the theorems that are callees of the callee of
current theorem in question. Click <<<<(hiding button), we can hide the
content that we expanded before.
<br>
in "Dependency Graph of Callee Theorems", click the hyperlink
<a
	href='../axiom/hierarchy.php?callee=axiom.discrete.combinatorics.binomial.theorem&deep=true'>callee</a>
, we can expand all the callee hiearchies, as follows:
<img class=zoom src="png/hierarchy/deep/callee.png" />
<hr />
<br>
<br>
<h4>Dependency Graph of Caller Theorems</h4>

<br>
in "Dependency Graph of Callee Theorems", click the hyperlink
<a
	href='../axiom/hierarchy.php?caller=axiom.discrete.combinatorics.binomial.theorem'>caller</a>
, we can view the Dependency Graph of Caller Theorems, as follows:
<img class=zoom src="png/hierarchy/caller.png" />
<hr />
the results above shows that during the process of proving 'binomial
theorem', we employed the following sub-theorems:
<ul>
	<li><a href='../axiom/discrete/combinatorics/binomial/Pascal'>axiom.discrete.combinatorics.binomial.Pascal</a>:
		<a href='https://en.wikipedia.org/wiki/Pascal%27s_rule'>Pascal's Rule</a>
		in Combinatorics, named after the French methematician Pascal.</li>
	<li><a href='../axiom/algebra/sufficient/imply/cond/induction'>axiom.algebra.sufficient.imply.cond.induction</a>:
		the first <a
		href='https://en.wikipedia.org/wiki/Mathematical_induction'>mathematical
			induction</a>, a method of recursively prooving mathematical theorems
		.</li>
</ul>
<br>

in "Dependency Graph of Callee Theorems", click the hyperlink
<a
	href='../axiom/hierarchy.php?caller=axiom.discrete.combinatorics.binomial.theorem&deep=true'>caller</a>
, we can expand the all callee hierarchies, as follows:
<img class=zoom src="png/hierarchy/deep/caller.png" />
<hr />
<br>
<hr />
<br>
<br>
<h2>Offline User Manual</h2>
For offline usage, the user must install the php web server. The
detailed installation instructions is provided here:
<a href='../php installation.docx'>php installation.docx</a>
. The user must also install the development environment of Python3.
Python3.6 is the most recommended. After install python3.6, a dependent
python package must be installed:
<br>
pip install mpmath
<br>
<br>
Now is the way to setup the theorem library on localhost using the
python source codes:
<br>
<br>
Take windows system as an example:
<h4></h4>
<li>designate a website folder, for example: E:\github, in accordance
	with the methods provided in php installation.docx, alter the
	DOCUMENT_ROOT of php server. Then we enter this document root:<br> cd
	E:\github
</li>
<br>
<li>use git to download the python source codes: <br> git clone
	--depth=1 <a href=https://github.com/cosmosZhou/sympy.git>https://github.com/cosmosZhou/sympy.git</a>
</li>
<br>
<li>enter the sympy folder: <br>cd sympy
</li>
<br>
<li>execute run, wherein debug=1 means output debugging information,
	while debug=0 means no debugging information:<br>python run.py debug=1

</li>
<br>
<li>after run.py is finished, the console will print the time lapse of
	the whole program, as well as the automatic prooving results of the
	whole theorem library, for example:<br> in all 868 axioms<br> unproved:<br>
	(the detail is omitted)....... <br> websites:<br> (the detail is
	omitted)....... <br> seconds costed = 45.13455533981323<br> minutes
	costed = 0.7522425889968872<br> total unproved = 22 <br> total failures
	= 0

</li>
<br>
<li>start the Chrome, or Edge/IE browser, input at the browser address
	bar:<br> <a href='../axiom'>http://localhost/sympy/axiom/</a><br>Now
	the visualized theorem library is instantiated. Then we can directly
	access this theorem library at localhost.
</li>
<br>
<hr />
<br>