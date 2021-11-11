# Qu'est-ce que axiom.top
  <br>
  
[axiom.top](../axiom.php) est un site Web pour le système de démonstration de théorème axiomatisé semi-mécanisé symbolique, basé sur un projet de calcul symbolique open-source de [sympy](https://github.com/sympy/sympy) et 
[Maxima](http://maxima.sourceforge.net), sa terminologie principale est définie selon les conventions de dénomination du système algébrique commercial 
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Ses principaux idéaux sont: la semi-mécanisation, l’axiomatisation et la poursuite de la justesse logique. À l’heure actuelle, il peut être utilisé pour effectuer des démonstrations semi-automatiques de théorèmes de manuels de mathématiques.  

* la semi-mécanisation mentionnée ci-dessus est définie de telle sorte que :
à l’heure actuelle, nous ne pouvons pas concevoir une machine entièrement automatique pour traiter les étapes de raisonnement logique de type humain dans la démonstration des théorèmes en fonction des conditions préalables et des conclusions données.
La machine ne peut résoudre le problème mathématique que selon les instructions fournies par les humains. Les humains doivent dire à l’ordinateur en cherchant dans la banque de connaissances axiomes, quels théorèmes ou axiomes appliquer devant un problème mathématique donné. 
* l’axiomatisation mentionnée ci-dessus est définie de telle sorte que :
chaque théorème mathématique, en dernière analyse, peut être prouvé par des axiomes qui sont indémontrables, qui sont supposés évidents, dont l’exactitude est supposée par les humains pour être vraie.
Toute la banque de connaissances sur les théorèmes mathématiques est construite étape par étape sur ces hypothèses vraisemblablement vraies. 

* la poursuite de l’exactitude logique mentionnée ci-dessus est définie de telle sorte que:
pendant le traitement du raisonnement, conformément aux énoncés définis dans
[Le programme de Hilbert](https://en.wikipedia.org/wiki/Hilbert%27s_program), le programme s’efforce d’être logiquement valide dans les grammaires définies par [langage formel]
(https://en.wikipedia.org/wiki/Formal_language).   
Chaque théorème est prouvé selon les hypothèses et l’exactitude de certains théorèmes ou axiomes précédemment prouvés. Dans ce projet, chaque problème mathématique sera exprimé sous la forme d’une déclaration [Python](https://www.python.org/) qui est définie avec précision sans ambiguïté qui peut émerger lorsque l’on utilise le langage naturel pour exprimer un problème mathématique.


Ce système est composé de trois éléments de base : [Symbole](.. /axiom.php?symbol=Symbol), [Fonction](.. /axiom.php?symbol=Function), Théorème; 
* Le symbole est un identificateur composé d’une série d’alphabets et de chiffres. Sa convention de nommage est la même que celle du langage de programmation [Python](https://www.python.org/).   
Il est utilisé pour définir n’importe quel symbole ou variable mathématique abstrait, par exemple:
n = Symbol(integer=True, positive=True, random=True, odd=True), désigne une variable aléatoire positive impaire,
p, q = Symbol(prime=True, even=False) indique que p est un nombre premier impair, donc est q;
m = Symbol(integer=True, nonnegative=True) désigne un entier non négatif,
t = Symbol(domain=Range(0, m)) désigne un entier compris entre 0 (y compris) et m (à l’exclusion de);
a = Symbol(integer=True, shape=(oo,)) désigne un vecteur infiniment grand d’entiers ;
b = Symbol(real=True, shape=(oo, oo)) désigne une matrice infiniment grande de réels ;
c = Symbol(complex=True, shape=(n, n, n)) désigne un tenseur complexe de forme n * n * n;
A = Symbol(etype=dtype.real, mesurable=True) désigne un ensemble de réels [mesurable](https://en.wikipedia.org/wiki/Measure_(mathématiques)), dans lequel etype est abrégé de « type d’élément »;
B = Symbol(etype=dtype.real, countable=True) désigne un ensemble [countable](https://en.wikipedia.org/wiki/Countable_set) de réels ;
C = Symbol(etype=dtype.integer, shape=(n,)) désigne un vecteur de n ensembles d’entiers ;
Q = Symbol(etype=dtype.rational.set) désigne un ensemble dont l’élément est un ensemble de rationnels ;    

* Fonction désigne un certain calcul mathématique sur d’autres symboles ou fonctions; par exemple:  
f, f1 = Function(real=True) indique que f, f1 sont toutes des fonctions réelles abstraites dont la définition est encore inconnue;   
g = Function(real=True, eval=lambda x: x \* x) désigne une fonction à valeur réelle définie comme : g(x) = x<sup>2</sup>;     
h = Function(etype=dtype.integer) désigne une fonction abstraite dont la valeur de retour est de type : integer set ;
f = Function(real=True, continuous=True) désigne une fonction à valeur réelle continue en un point donné ;
f = Function(real=True, differentiable=True) désigne une fonction à valeur réelle différentiable en un point donné;    
f = Function(mesurable=True, domain=Interval(0, 1)) désigne une fonction mesurable à valeur réelle dont la valeur se trouve dans le domaine [0, 1];
f = Function(real=True, integrable=True) désigne une fonction à valeur réelle Lebesgue-intégrable à un intervalle donné;    
ainsi que la fonction intégrée au système, telle que [cos](../axiom.php?symbol=cos)(x), [sin](../axiom.php?symbol=sin)(x), [tan](../axiom.php?symbol=tan)(x), [log](../axiom.php?symbol=log)(x), [exp](../axiom.php?symbol=exp)(x), et quelques opérateurs plus complexes [Sum](../axiom.php?symbol=Sum)\[k:a:b\](h\[k\]), [Product](../axiom.php?symbol=Product)\[k:a:b\](h\[k\]), [ForAll](../axiom.php?symbol=All)\[k:a:b\](h\[k\] > t\[k\]), [Exists](../axiom.php?symbol=Any)\[k:a:b\](h\[k\] > t\[k\]), etc.  
Toutes ces fonctions n’effectueront aucun calcul en virgule flottante comme d’habitude, car au cours du processus de preuve mathématique, toute implication de calculs avec des valeurs à virgule flottante entraînera une erreur logique en mathématiques pures.
Chaque valeur dans la preuve mathématique est au sens strict une valeur mathématique, il n’y a pas de concept de valeurs approximatives comme les valeurs à virgule flottante;      


* Théorème désigne un théorème qui est prouvable ou un axiome qui est indémontrable ;
Les entrées des théorèmes doivent être des expressions ou des conditions, ses sorties sont nécessairement des conditions. Il est stocké dans une base de données mysql en tant que banque de connaissances sur les théorèmes. Son utilisation principale est la suivante: Theorem.apply(...); par exemple:    
a, b, c = Symbol(complex=True)  
[algebra.poly_is_zero.imply.et.infer.cubic.apply](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.cubic)(Equal(x ** 3 + a * x ** 2 + b * x + c, 0), x=x), désigne le processus de détermination d’une équation cubique dans le domaine des complexes.     
   
   
L’ensemble du système de numérotation est défini comme suit :  
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


# La construction du répertoire des théorèmes mathématiques
  <br>
  
Au moment d’écrire ces lignes, <label id=count>____</label> théorèmes ont été réenregistrés dans le répertoire des théorèmes, qui peuvent être appliqués dans un système axiomatisé semi-mécanisé de démonstration de théorèmes mathématiques.
Il est principalement composé de:  
  	
* [algebra](../axiom.php?module=algebra) fait référence à l’algèbre élémentaire, qui se penche principalement sur les techniques de transformation des équations、 substitution de symboles, séries finies [∑ telescoping](../axiom.php?module=algebra.sum.to.add.telescope)、∏ le télescopage de produit, propriété de la transitivité pour les inégalités, résolution [équations simples](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.simple_equation), [équations quadratiques](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.quadratic), [équations cubiques](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.cubic) et [équations quartiques](../axiom.php?module=algebra.poly_is_zero.imply.et.infer.quartic), propriétés communes de certaines fonctions élémentaires, ainsi que la preuve de [méthode d’induction mathématique](../axiom.php?module=algebra.ne_zero.infer.imply.ne_zero.induct);   
* [sets] (.. /axiom.php?module=sets) fait référence à la théorie des ensembles, qui est le fondement des théories de la preuve et de l’analyse mathématiques entières. Cela implique beaucoup de propositions utilisant les terminologies comme
ForAll, Exists, Element, Subset, par exemple : 
la preuve du [principe d’inclusion-exclusion](../axiom.php?module=sets/imply/eq/principle/inclusion_exclusion/basic). On peut dire ainsi que : la théorie des ensembles est la grammaire fondamentale de la démonstration automatique des théorèmes.  
* [geometry](../axiom.php?module=geometry) est composé d’une école de premier cycle et d’un collège
[géométrie plane](../axiom.php?module=geometry/plane), trigonométrie et collège
[géométrie solide](../axiom.php?module=geometry/solid), certaines identités trigonométriques, par exemple :
[principe d’addition du cosinus](../axiom.php?module=geometry.cos.to.add.principle.add), [principe de produit de la trigonométrie](../axiom.php?module=geometry.mul.to.add.sin), et ainsi de suite.   
* [calculus](../axiom.php?module=calculus) comprend :
[la définition de la limite](../axiom.php?module=calculus/eq/to/any_all/limit_definition) et ses théories fondamentales qui sont la base théorique du calcul.  
propriétés opérationnelles de [série infinie](../axiom.php?module=calculus.eq.imply.eq.series.infinite.coefficient); 
preuve de [intégration par parties](../axiom.php?module=calculus.integral.to.add.by_parts);  
détermination d’une intégrale pour certaines fonctions transcendantales;  
* [discrete](../axiom.php?module=discrete) la section comprend la théorie des nombres, les mathématiques discrètes, la combinatoire, l’algèbre linéaire, certaines techniques de comptage de base impliquant des permutations (telles que
[permutations](../axiom.php?module=discrete.abs_cup.to.factorial), induction combinatoire pour [deuxième nombre de Stirling](../axiom.php?module=discrete.stirling2.to.add.recurrence),  
dérivation pour [Nombre catalan](../axiom.php?module=discrete.eq.eq.imply.eq.catalan.recurrence)， 
bases de [fraction continue](../axiom.php?module=discrete.add.to.pow.HK.recurrence); ainsi que des propositions de déterminant de matrice.  
* [stats](../axiom.php?module=stats) fait référence à la statistique et à la théorie des probabilités, comprenant: la dérivation de la formule de densité de probabilité d’une distribution commune (telle que, la distribution binomiale, la distribution gaussienne, la distribution de Poisson, la distribution de die, Χ<sup>2</sup>distribution)，ainsi que des propositions liées au [théorème de Bayes](../axiom.php?module=stats/probability/to/mul);  
* [keras](../axiom.php?module=keras) est liée aux théories mathématiques derrière les techniques contemporaines d’apprentissage profond / apprentissage automatique, y compris la modélisation mathématique utilisée dans le traitement / compréhension du langage naturel, comme la formule d’inférence avant ou de propagation en arrière de
[LSTM](https://www.mitpressjournals.org/doi/pdf/10.1162/089976600300015015),
[BERT](https://arxiv.org/abs/1706.03762),
[TEXT-CNN](https://arxiv.org/pdf/1408.5882.pdf),
Champ aléatoire conditionnel [CRF](https://arxiv.org/abs/1603.01360), 
et preuve partielle de KMeans
[convergence des regroupements](../axiom.php?module=sets.el.notin.le.imply.le.st.variance). La théorie des probabilités fournit la base théorique fondamentale de l’apprentissage automatique afin que cette technique contemporaine puisse être explicable.  
* Dans un avenir proche, des sections pour la physique, la chimie, la biologie et leurs sous-divisions seront créées pour révéler le développement de découvertes scientifiques qui ont été couronnées de succès grâce à l’application de l’analyse mathématique.  
<br><br>
-------
Ce nouveau système de démonstration de théorème axiomatisé semi-mécanisé peut simplifier les étapes de raisonnement dans l’analyse mathématique, atteignant ainsi l’idéal de « brancher les dynamos de la pensée ». Le chercheur n’a qu’à maîtriser le macro squelette du raisonnement, laissant le calcul détaillé à l’ordinateur. Il peut être appliqué pour la preuve mathématique théorique, ce qui peut être utile pour fournir une référence ou des conseils au cours de l’analyse mathématique pour les ingénieurs en algorithmes, chercheurs dans leurs travaux de recherche. Il peut également être utilisé pour les chercheurs en mathématiques pour gérer et éditer leurs articles théoriques, sans avoir besoin d’édition manuelle de formules mathématiques puisque l’impression au latex est automatiquement générée par programmation. On peut même utiliser l’environnement de développement intégré (IDE) en ligne pour [Python] (https://www.python.org/) pour éditer les théorèmes mathématiques afin de terminer les travaux de recherche théorique. L’IDE [Python] (https://www.python.org/) en ligne fournit un puissant raccourci clavier F3 permettant aux utilisateurs de localiser instantanément la définition de n’importe quel symbole ou fonction. Il est d’une utilité pratique pour la recherche théorique, la recherche industrielle ou à des fins pédagogiques. Il s’agit d’un ouvrage de référence en ligne pour les théorèmes mathématiques et les modèles algorithmiques pour l’industrie.
<br><br>


<script	src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>

<script>
	$('#count').load("/sympy/php/request/count.php");
</script>