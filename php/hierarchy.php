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

$key_input = array_keys($_GET)[0];

switch ($key_input) {
    case "callee":
        $key = 'caller';
        $invert = true;
        break;

    case "caller":
        $key = 'callee';
        $invert = false;
        break;
}

$module = $_GET[$key_input];

// error_log("module = " . $module);
$graph = mysql\establish_hierarchy($module, $invert);

$deep_invert = \std\jsonify(! $deep);

// error_log("deep_invert = " . $deep_invert);
$graph->convert_set_to_list();
$cyclic_proof = $graph->detect_cycle($module);

?>

<div id=root>
	<information></information>
	<template v-if="cyclic_proof">
		<font color=red>cyclic proof detected in :</font><br> cyclic proof =
		<href :module=cyclic_proof></href>
		<br>
		<href :module=module />

	</template>
	<template v-else>
		<module :module=module />
	</template>

</div>

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.5.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="/sympy/js/utility.js"></script>
<script>
	var data = {
		module : <?php echo \std\jsonify($module)?>,
		graph : <?php echo \std\jsonify($graph)?>,
		cyclic_proof: <?php echo \std\jsonify($cyclic_proof)?>,
		root : null		
	};

	var information = {
        name: 'information',
        data: function() {
        	return {
        		key_input : <?php echo \std\jsonify($key_input)?>,
        		key : <?php echo \std\jsonify($key)?>,
        		deep: <?php echo $deep_invert?>
   	     	};
   	    },
        
        props: [],
        template:
            `<div>
				the axiom in question is a 
				<a :href="'hierarchy.php?' + key_input + '=' + this.$parent.module + '&deep=' + deep" :title="'show ' + (deep?'deep':'only first-layer') + ' hierarchy'">{{key_input}}</a>
				in the following hierarchy, would you switch to 
				<a :href="'hierarchy.php?' + key + '=' + this.$parent.module">{{key}}</a> hierarchy?
			</div>`
    };
	
	
	var href = {
        name: 'href',
        props: ['module'],        
        template: 
        	`<a :href="'/sympy/axiom.php/' + module.replace(/\\./g, '/')">{{module}}</a>`
    };
	
	var module = {
        name: 'module',
        data: function() {
            	return {
            		root: this.$parent.root == null ? this.$parent: this.$parent.root
       	     	};
       	     },
        props: ['module'],        
        template:
        	`<li>
        		<href :module=module />
        		<template v-if="module in root.graph">        			
        			<button class=transparent onmouseover="this.style.backgroundColor='red'" onmouseout="this.style.backgroundColor='rgb(199, 237, 204)'">>>>></button>
        		 	<ul class=hidden>    				     				
        	 			<module :module=module v-for="module of root.graph[module]" />
        			</ul>
    			</template>				
            </li>`,
        components : {
            href: href
        }
    };

	var components = {
		module : module,
		href: href, 
		information: information
	};
	
	var app = new Vue({
		el : '#root',
		data : data, 
		components : components
	});

	toggle_expansion_button();
	
	var deep = <?php echo \std\jsonify($deep)?>;
	if (deep)
		click_all_expansion_buttons();
	else
		click_first_expansion_button();

</script>

