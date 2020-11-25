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

function depict(&$dict, $module, $multiplier)
{
    // https://www.php.net/manual/en/function.str-repeat.php
    echo str_repeat("&nbsp;", $multiplier) . to_a_tag($module) . "<br>";
    if (array_key_exists($module, $dict)) {
        foreach ($dict[$module] as $module => $value) {
            depict($dict, $module, $multiplier + 8);
        }
    }
}

if (array_key_exists('callee', $_GET)) {    
    echo "the axiom in question is a callee in the following hierarchy:<br>";
    $dict = [];
    foreach (read_all_axioms(dirname(__file__)) as $py) {
        $caller = to_python_module($py);
        $modules = process_py($py);

        foreach ($modules as $callee) {
            if (! array_key_exists($callee, $dict)) {
                $dict[$callee] = [];
            }

            if (! array_key_exists($caller, $dict[$callee])) {
                $dict[$callee][$caller] = 0;
            }
            ++ $dict[$callee][$caller];
        }
    }
    
    $callee = $_GET['callee'];
    depict($dict, $callee, 2);    
    echo "<br><br>switch to <a href='request.php?caller=$callee'>caller hierarchy</a>";
} else if (array_key_exists('caller', $_GET)) {
    
    echo "the axiom in question is a caller in the following hierarchy:<br>";
    $dict = [];
    foreach (read_all_axioms(dirname(__file__)) as $py) {
        $caller = to_python_module($py);
        $modules = process_py($py);

        foreach ($modules as $callee) {
            if (! array_key_exists($caller, $dict)) {
                $dict[$caller] = [];
            }

            if (! array_key_exists($callee, $dict[$caller])) {
                $dict[$caller][$callee] = 0;
            }
            ++ $dict[$caller][$callee];
        }
    }
    
    $caller = $_GET['caller'];
    depict($dict, $caller, 2);
    echo "<br><br>switch to <a href='request.php?callee=$caller'>callee hierarchy</a>";
}

// exit(0);

?>