<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<title>hierarchy</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';

// ^ *error_log

$array_keys = array_keys($_GET);

if (count($array_keys) > 1) {
    // print_r($_GET);
    $deep = json_decode($_GET['deep']);
    unset($_GET['deep']);
} else {
    $deep = false;
}

$keyInput = array_keys($_GET)[0];

switch ($keyInput) {
    case "callee":
        $key = 'caller';
        $invert = true;
        break;

    case "caller":
        $key = 'callee';
        $invert = false;
        break;
}

$module = $_GET[$keyInput];

$graph = mysql\establish_hierarchy($module, $invert);

// $graph->convert_set_to_list();
$graph->detect_cycle_traceback($module, $parent);

if ($parent) {
//     echo implode('<br>', $parent)."<br>";
    
    $cyclicProof = $parent[0];

    for ($i = 1; $i < count($parent); ++ $i) {
        if ($parent[$i] == $cyclicProof) {
            break;
        }
    }

    $parent[] = $module;
    
    $traceback = [];
    for ($j = count($parent) - 1; $j >= $i; -- $j) {
        $traceback[] = $parent[$j];
    }    
    
//     echo implode('<br>', $traceback)."<br>";
    
} else {
    $traceback = null;
}
?>

<div id=root>
	<hierarchy :module=module :graph=graph :traceback=traceback :deep=deep
		:key-input=keyInput></hierarchy>
</div>

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.5.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script src="/sympy/js/std.js"></script>
<script src="/sympy/js/utility.js"></script>
<script>
	var data = {
		module : <?php echo \std\jsonify($module)?>,
		graph : <?php echo \std\jsonify($graph)?>,
		traceback: <?php echo \std\jsonify($traceback)?>,
		keyInput : <?php echo \std\jsonify($keyInput)?>,
        deep: <?php echo \std\jsonify($deep)?>,
	};

	Vue.use(httpVueLoader);
	Vue.component('hierarchy', 'url:/sympy/vue/hierarchy.vue');
		
	var app = new Vue({
		el : '#root',
		data : data,
	});
	
</script>

