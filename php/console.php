<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<title>console</title>
<?php
require_once 'std.php';

$statements[] = [
    'script' => '',
    'latex' => ''
];

?>

<div id=root>
	<console :statements=statements></console>
</div>

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"></script>

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
		updated() {
			MathJax.typesetPromise();
		},                
    });
    
//    var user = sympy_user();
// 	request_get(`/${user}/run.py?console=True`, {}).done(res => {
// 		console.log('res = ' + res);
// 	}).fail(fail);
	
// 	window.onbeforeunload = function() {
// 		request_get('http://localhost:5000/kill', {}).done(res => {
// 			console.log('res = ' + res);
// 		}).fail(fail);
// 	};
//https://blog.csdn.net/yaojie5519/article/details/109577384?utm_medium=distribute.pc_relevant.none-task-blog-2%7Edefault%7EBlogCommendFromMachineLearnPai2%7Edefault-14.control&depth_1-utm_source=distribute.pc_relevant.none-task-blog-2%7Edefault%7EBlogCommendFromMachineLearnPai2%7Edefault-14.control			
</script>
