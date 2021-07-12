<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<title>console</title>
<?php
require_once '../std.php';

$statements = [
    [
        'script' => 'x = Symbol.x(real=True)',
        'latex' => ''
    ],
    [
        'script' => 'y = Symbol.y(real=True)',
        'latex' => ''
    ],
    [
        'script' => 'z = Symbol.z(real=True)',
        'latex' => ''
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '(-y + sqrt(y * y - 4 * x * z)) / (2 * x)',
        'latex' => '$$\\frac{\\sqrt{y^{2} - 4 x z} - y}{2 x}$$'
    ],
    [
        'script' => '',
        'latex' => ''
    ],
];

?>

<div id=root>
	<console :statements=statements></console>
</div>

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>

<script async
	src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>

<script src="/sympy/js/std.js"></script>
<script src="/sympy/js/utility.js"></script>
<script>
	MathJax = {
		tex: {
	      inlineMath: [['$', '$'], ['\\(', '\\)']], 
    	  displayMath: [["$$", "$$"], ["\\[", "\\]"]],
	    }
	};

    var data = {
        statements : <?php echo \std\jsonify($statements)?>,
    };

    Vue.use(httpVueLoader);
    Vue.component('console', 'url:/sympy/vue/console.vue');
        
    var app = new Vue({
        el : '#root',
        data : data,
    });    
</script>
