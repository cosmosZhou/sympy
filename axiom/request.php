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

function module_pieced_together_in_apply(&$statement, &$axiom_prefix, &$input)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False)
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];
        // error_log('module_pieced_together: ' . __LINE__);
        $input[] = module_pieced_together($theorem, $statement, $axiom_prefix);
    }
}

function module_pieced_together($theorem, &$statement, &$axiom_prefix)
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

    $prefix = $axiom_prefix[$head];

    if ($prefix) {
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
    $py = file($py);
    for ($i = 0; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        // from axiom.neuron import bilinear # python import statement
        if (preg_match('/^from +(.+) +import +(.*)/', $statement, $matches)) {

            $prefix = $matches[1];
            $namespaces = $matches[2];
            $namespaces = preg_split("/[\s,]+/", $namespaces, - 1, PREG_SPLIT_NO_EMPTY);

            // error_log("end(namespaces) = " . end($namespaces));
            if (! strcmp(end($namespaces), '\\')) {
                // error_log("strcmp = " . strcmp(end($namespaces), '\\'));
                array_pop($namespaces);

                $statement = $py[++ $i];
                // error_log("$statement");

                $namespaces_addition = preg_split("/[\s,]+/", $statement, - 1, PREG_SPLIT_NO_EMPTY);
                // error_log("namespaces_addition = " . jsonify($namespaces_addition));

                $namespaces = array_merge($namespaces, $namespaces_addition);

                // error_log("namespaces = " . jsonify($namespaces));
            }

            $prefix_path = str_replace(".", "/", $prefix);

            foreach ($namespaces as $namespace) {
                // error_log('prefix detected: ' . $prefix . '.' . $namespace);
                $axiom_prefix[$namespace] = $prefix_path;
            }

            continue;
        }

        if (preg_match('/^import +(.+)/', $statement, $matches)) {
            // error_log('import statement: ' . $statement);
            $packages = $matches[1];
            $packages = preg_split("/\s*,\s*/", $packages, - 1, PREG_SPLIT_NO_EMPTY);

            foreach ($packages as $package) {
                $package = preg_split("/\s+/", $package, - 1, PREG_SPLIT_NO_EMPTY);
                // error_log('count(package) = ' . count($package));

                switch (count($package)) {
                    case 1:
                        $package = $package[0];
                        $axiom_prefix[$package] = '';
                        break;
                    case 2:
                        // error_log('count(package[0]) = ' . $package[0]);
                        // error_log('count(package[1]) = ' . $package[1]);
                        break;
                    case 3:
                        // error_log('count(package[0]) = ' . $package[0]);
                        // error_log('count(package[1]) = ' . $package[1]);
                        // error_log('count(package[2]) = ' . $package[2]);
                        $axiom_prefix[end($package)] = '';
                        // error_log('package detected: ' . $package[0]);
                        break;
                    default:
                        break;
                }
            }

            continue;
        }

        if (preg_match('/^def +prove\(Eq(, *\w+)?\) *: */', $statement, $matches)) {
            // error_log('prove begins: ' . $statement);
            break;
        }
    }

    // echo 'axiom_prefix: ' . jsonify($axiom_prefix);

    $lengths = [];
    $input = [];
    $inputs = [];
    for (++ $i; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        $statement = rtrim($statement);
        // remove comments starting with #
        if (preg_match('/^\s*#.*/', $statement, $matches) || ! $statement) {
            continue;
        }

        // the start of the next global statement other than def prove
        if (! startsWith($statement, '    ')) {
            break;
        }

        $statement = substr($statement, 4);

        if (preg_match('/([\w.]+)\.apply\(/', $statement, $matches)) {
            $theorem = $matches[1];
            // error_log('theorem detected: ' . $theorem);

            if (startsWith($theorem, '.')) {
                // consider the case
                // Eq << Eq[-1].reversed.apply(axiom.discrete.sets.inequality.notcontains, evaluate=False)
                module_pieced_together_in_apply($statement, $axiom_prefix, $input);
            } else if (strpos($theorem, 'Eq.') === false) {

                // error_log('module_pieced_together: ' . __LINE__);
                // error_log("statement = $statement");
                $input[] = module_pieced_together($theorem, $statement, $axiom_prefix);
            } else {
                module_pieced_together_in_apply($statement, $axiom_prefix, $input);
            }
        } else if (preg_match('/= *apply\(/', $statement, $matches)) {
            module_pieced_together_in_apply($statement, $axiom_prefix, $input);
        } else {
            module_pieced_together_in_apply($statement, $axiom_prefix, $input);
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            if ($input) {
                $inputs = array_merge($inputs, $input);
                unset($input);
            }

            $lengths[] = 1;
        } else if (preg_match('/(Eq\.\w+ *(?:, *(?:Eq\.\w+|\w+|\*\w+) *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            // error_log("parameter: " . $statement);

            preg_match_all('/Eq\.\w+/', $statement, $matches, PREG_SET_ORDER);

            $lengths[] = count($matches);
            if ($input) {
                $inputs = array_merge($inputs, $input);
                unset($input);
            }
        } else {
            // error_log("python statements: $statement");
        }
    }
    return $inputs;
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

class Node
{

    private $descendent;

    public function __construct()
    {
        $this->descendent = [];
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

echo "the axiom in question is a $key_input in the following hierarchy, would you switch to <a href='request.php?$key=$module'>$key hierarchy</a>?<br>";

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

javaScript("click_first_expansion_button();");

?>