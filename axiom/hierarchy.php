<?php
include_once 'index.html';
require_once 'utility.php';

function read_all_axioms($dir)
{
    foreach (read_directory($dir) as $directory) {
        foreach (read_all_files($directory, 'py') as $py) {
            if (strcmp(basename($py), "__init__.py")) {
                yield [
                    $py,
                    substr($py, 0, - 2) . 'php'
                ];
            } else {
                yield [
                    $py,
                    substr($py, 0, - strlen('/__init__.py')) . '.php'
                ];
            }
        }
    }
}

function module_pieced_together($theorem, &$axiom_prefix)
{
    // error_log("theorem = $theorem");
    // error_log("statement = $statement");
    // error_log("axiom_prefix = " . jsonify($axiom_prefix));
    // error_log("__file__ = " . __file__);
    // error_log("dirname(__file__) = " . dirname(__file__));
    $dot_index = strpos($theorem, '.');
    if ($dot_index === false) {
        $head = $theorem;
    } else {
        $head = substr($theorem, 0, $dot_index);
    }

    if (strlen($head)) {
        $prefix = $axiom_prefix[$head];
        $prefix = str_replace('/', '.', $prefix);
        $module = "$prefix.$theorem";
    } else {
        $module = $theorem;
    }

    return $module;
}

// input is a py file
function process_py($py)
{
    $axioms = [];

    foreach (yield_from_py($py) as $dict) {
        // error_log(jsonify($dict));

        if (array_key_exists('axiom_prefix', $dict)) {
            $axiom_prefix = $dict['axiom_prefix'];
        } else if (array_key_exists('a', $dict)) {
            foreach ($dict['a'] as &$axiom) {
                $axioms[] = module_pieced_together($axiom, $axiom_prefix);
            }
        }
    }
    return $axioms;
}

class Set
{

    private $set;

    public function __construct()
    {
        $this->set = [];
    }

    public function add($element)
    {
        $this->set[$element] = true;
    }

    public function remove($element)
    {
        unset($this->set[$element]);
    }

    public function enumerate()
    {
        foreach ($this->set as $key => &$_) {
            yield $key;
        }
    }

    public function contains($element)
    {
        return array_key_exists($element, $this->set);
    }
}

class Graph
{

    public $graph;

    private $permanent_mark;

    private $temporary_mark;

    function visit($n)
    {
        // error_log("visiting key = $n");
        if ($this->permanent_mark->contains($n))
            return null;

        if ($this->temporary_mark->contains($n))
            return $n;

        if (array_key_exists($n, $this->graph)) {

            $this->temporary_mark->add($n);
            // error_log("this->graph[n] = " . jsonify($this->graph[$n]));

            foreach ($this->graph[$n] as $m) {
                $node = $this->visit($m);
                if ($node != null)
                    return $node;
            }

            $this->temporary_mark->remove($n);
        }

        $this->permanent_mark->add($n);
        return null;
    }

    function initialize_topology()
    {
        $this->permanent_mark = new Set();
        $this->temporary_mark = new Set();
    }

    function &topological_sort_depth_first()
    {
        $this->initialize_topology();
        foreach ($this->graph as $n => $_) {
            if ($this->visit($n))
                return null;
        }

        return $this->L;
    }

    function detect_cyclic_proof($key)
    {
        $this->initialize_topology();
        return $this->visit($key);
    }

    public function __construct()
    {
        $this->graph = [];
    }

    function convert_set_to_list()
    {
        foreach ($this->graph as $key => &$value) {
            $this->graph[$key] = iterator_to_array($value->enumerate());
        }
    }

    function add_edge($from, $to)
    {
        if (! array_key_exists($from, $this->graph)) {
            $this->graph[$from] = new Set();
        }

        $this->graph[$from]->add($to);
    }
}

$mapping = new Graph();

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

foreach (read_all_axioms(dirname(__file__)) as list ($py, $php)) {
    $from = to_python_module($php);
    $modules = process_py($py);

    foreach ($modules as $to) {
        if ($invert)
            $mapping->add_edge($to, $from);
        else
            $mapping->add_edge($from, $to);
    }
}

$module = $_GET[$key_input];

$deep_invert = jsonify(! $deep);

$mapping->convert_set_to_list();
$cyclic_proof = $mapping->detect_cyclic_proof($module);

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
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>

<script src="utility.js"></script>

<script>	
	var data = {
		module : <?php echo jsonify($module)?>,
		graph : <?php echo jsonify($mapping->graph)?>,
		cyclic_proof: <?php echo jsonify($cyclic_proof)?>,
		root : null		
	};

	var information = {
        name: 'information',
        data: function() {
        	return {
        		key_input : <?php echo jsonify($key_input)?>,
        		key : <?php echo jsonify($key)?>,
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
        	`<a :href="'/sympy/' + module.replaceAll('.', '/') + '.php'">{{module}}</a>`
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
        			<button onmouseover="this.style.backgroundColor='red'" onmouseout="this.style.backgroundColor='rgb(199, 237, 204)'">>>>></button>
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
	
	var deep = <?php echo jsonify($deep)?>;
	if (deep)
		click_all_expansion_buttons();
	else
		click_first_expansion_button();

</script>

