<!DOCTYPE html>
<meta charset="UTF-8">
<?php
require_once 'utility.php';

if (array_key_exists('module', $_GET)) {
    $module = $_GET['module'];
} else {
    $module = "";
}

$size = $module ? strlen($module) : 32;

list ($apply, $prove) = fetch_codes($module, true);

error_log("apply = " . \std\jsonify($apply));
error_log("prove = " . \std\jsonify($prove));

?>

<title>new theorem</title>
<link rel=stylesheet
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.css" />
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/theme/eclipse.css">
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.css">

<link rel="stylesheet" href="/sympy/css/codemirror.css">
<link rel="stylesheet" href="/sympy/css/style.css">

<div id=root>
	<new-theorem :module=module :apply=apply :prove=prove></new-theorem>
</div>

<script src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/mode/python/python.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.js"></script>
<script src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/edit/matchbrackets.js"></script>
<script src="https://cdn.jsdelivr.net/npm/jquery@3.5.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script src="/sympy/js/std.js"></script>	
<script src="/sympy/js/utility.js"></script>
<script>
	var data = {
        apply : <?php echo \std\jsonify($apply)?>,
        prove : <?php echo \std\jsonify($prove)?>,
        module : <?php echo \std\jsonify($module)?>,
    };

    Vue.use(httpVueLoader);
    Vue.component('new-theorem', 'url:/sympy/vue/new-theorem.vue');
        
    var app = new Vue({
        el : '#root',
        data : data,
    });	
</script>