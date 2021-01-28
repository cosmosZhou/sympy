<?php
include_once 'index.html';
require_once 'utility.php';

function read_all_axioms($dir)
{
    foreach (read_directory($dir) as $directory) {
        foreach (read_all_files($directory, 'py') as $py) {
            if (strcmp(basename($py), "__init__.py")) {
                yield $py;
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

global $sagemath;

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

    private $graph;

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

    function depict($module, $multiplier)
    {
        // https://www.php.net/manual/en/function.str-repeat.php
        echo str_repeat("&nbsp;", $multiplier) . to_a_tag($module);

        if (array_key_exists($module, $this->graph)) {
            echo "<button onmouseover=\"this.style.backgroundColor='red';\" onmouseout=\"this.style.backgroundColor='rgb(199, 237, 204)';\">>>>></button>";
            echo "<div class=hidden>";
            foreach ($this->graph[$module] as $module) {
                $this->depict($module, $multiplier + 8);
            }
            echo "</div>";
        }
        echo "<br>";
    }

    function depict_topology()
    {
        foreach ($this->permanent_mark->enumerate() as $module) {
            echo str_repeat("&nbsp;", 8) . to_a_tag($module) . "<br>";
        }
    }
}

$mapping = new Graph();

$array_keys = array_keys($_GET);

if (count($array_keys) > 1) {
//     print_r($_GET);
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

foreach (read_all_axioms(dirname(__file__)) as $py) {
    $from = to_python_module($py);
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

echo "the axiom in question is a <a href='request.php?$key_input=$module&deep=$deep_invert'>$key_input</a> in the following hierarchy, would you switch to <a href='request.php?$key=$module'>$key</a> hierarchy?<br>";

$mapping->convert_set_to_list();

$pinpoint = $mapping->detect_cyclic_proof($module);
if ($pinpoint) {
    echo "<font color=red>cyclic proof detected in :</font><br>";
    echo to_a_tag($module) . "<br>";
    if (strcmp($pinpoint, $module)) {
        echo str_repeat("&nbsp;", 8) . to_a_tag($pinpoint) . "<br>";
    } else {
        // $mapping->depict_topology();
    }
} else {
    $mapping->depict($module, 2);
}

function javaScript($js)
{
    echo "<script>" . $js . "</script>";
}

javaScript("toggle_expansion_button();");

if ($deep)
    javaScript("click_all_expansion_buttons();");
else
    javaScript("click_first_expansion_button();");

?>