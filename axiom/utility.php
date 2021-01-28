<?php
include_once 'index.html';

// include_once dirname(dirname(__FILE__)) . '/index.html';

// use the following regex to remove error_log prints:^ +error_log
// to speed up the .php page rendering, disable error_log!!
function get_extension($file)
{
    return pathinfo($file, PATHINFO_EXTENSION);
}

function startsWith($haystack, $needle)
{
    $length = strlen($needle);
    return substr($haystack, 0, $length) === $needle;
}

function endsWith($haystack, $needle)
{
    $length = strlen($needle);
    if ($length == 0) {
        return true;
    }

    return substr($haystack, - $length) === $needle;
}

function quote($param)
{
    if (strpos($param, "'") !== false) {
        $param = str_replace("'", "&apos;", $param);
    }

    return $param;
}

function to_python_module($py)
{
    global $sagemath;
    $module = [];
    $pythonFile = $py;
    for (;;) {
        $dirname = dirname($pythonFile);
        $basename = basename($pythonFile);
        if (! strcmp($basename, $sagemath)) {
            break;
        }

        $module[] = $basename;
        $pythonFile = $dirname;
    }

    $module[0] = substr($module[0], 0, - strlen(get_extension($module[0])) - 1);
    $module = array_reverse($module);

    $module = join('.', $module);
    return $module;
}

function &yield_from_php($php)
{
    foreach (file($php) as &$statement) {
        // error_log($statement);
        if (strncmp($statement, "//", 2) !== 0) {
            continue;
        }

        $statement = substr($statement, 2);
        yield $statement;
    }
}

function reference(&$value)
{
    if (is_array($value)) {
        foreach ($value as &$element) {
            $element = reference($element);
        }
        $value = join(', ', $value);
        return $value;
    }
    if (preg_match('/\d+/', $value, $matches)) {
        $value = (int) $value;
        if ($value < 0)
            return "plausible";
        return "Eq[$value]";
    } else {
        return "Eq.$value";
    }
}

function jsonify($param)
{
    return json_encode($param, JSON_UNESCAPED_UNICODE);
}

function println($param, $file = null)
{
    if (is_array($param)) {
        $param = jsonify($param);
    }

    if ($file) {
        echo "called in $file:<br>";
    }
    print_r($param);
    print_r("<br>");
}

// function get_extension($file)
// {
// substr(strrchr($file, '.'), 1);
// }

// function get_extension($file)
// {
// return substr($file, strrpos($file, '.') + 1);
// }

// function get_extension($file)
// {
// return end(explode('.', $file));
// }

// function get_extension($file)
// {
// $info = pathinfo($file);
// return $info['extension'];
// }
function read_directory($dir)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (is_dir($temp)) {
                    yield $temp;
                }
            }
        }
    }
}

function read_files($dir, $ext = null)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                $temp = $dir . DIRECTORY_SEPARATOR . $fl;
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                if (! is_dir($temp)) {
                    if ($ext == null || ! strcmp(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
        }
    }
}

function to_a_tag($module)
{
    $href = str_replace('.', '/', $module);
    global $sagemath;
    $href = "/$sagemath/$href.php";
    return "<a name=python[] href='$href'>$module</a>";
}

function read_all_files($dir, $ext)
{
    if (is_dir($dir)) {

        $handle = opendir($dir);

        if ($handle) {
            while (($fl = readdir($handle)) !== false) {
                if ($fl == '.' || $fl == '..') {
                    continue;
                }

                $temp = $dir . DIRECTORY_SEPARATOR . $fl;

                if (is_dir($temp)) {
                    // echo 'directory : ' . $temp . '<br>';
                    yield from read_all_files($temp, $ext);
                } else {
                    if (! strcmp(get_extension($temp), $ext)) {
                        yield $temp;
                    }
                }
            }
        }
    }
}

function removedir($dir)
{
    foreach (read_files($dir) as $file) {
        unlink($file);
    }

    foreach (read_directory($dir) as $subdir) {
        removedir($subdir);
    }
    rmdir($dir);
}

function is_latex($latex, &$matches)
{
    if (preg_match_all('/\\\\\[.+?\\\\\]/', $latex, $matches, PREG_SET_ORDER)) {
        return true;
    }
    return false;
}

function is_def_start($funcname, $statement, &$matches)
{
    return preg_match("/^def +$funcname\([^)]*\) *: */", $statement, $matches);
}

function recursive_construct($parentheses, $depth)
{
    $mid = strlen($parentheses) / 2;
    $start = substr($parentheses, 0, $mid);
    $end = substr($parentheses, $mid);

    if (need_escape($start)) {
        $start = "\\" . $start;
        $end = "\\" . $end;
    }

    if ($depth == 1)
        return "${start}[^$parentheses]*$end";
    return "${start}[^$parentheses]*(?:" . recursive_construct($parentheses, $depth - 1) . "[^$parentheses]*)*$end";
}

function balancedGroups($parentheses, $depth, $multiple = true)
{
    $regex = recursive_construct($parentheses, $depth);
    if ($multiple)
        return "((?:$regex)*)";
    else
        return "(?:$regex)";
}

function balancedParentheses($depth, $multiple = false)
{
    return balancedGroups("()", $depth, $multiple);
}

function balancedBrackets($depth, $multiple = false)
{
    return balancedGroups("\[\]", $depth, $multiple);
}

function need_escape($s)
{
    switch ($s) {
        case "(":
        case ")":
        case "{":
        case "}":
            return true;
        default:
            return false;
    }
}

function numOfYields($statement)
{
    global $patternOfYield;

    if (preg_match_u("/^$patternOfYield,?$/", $statement, $matches)) {
        // error_log("match one yield: " . $matches[1]);
        return 1;
    } else {
        // error_log('return ' . $statement);
        if (preg_match_u("/^$patternOfYield,\s*([\s\S]+)$/", $statement, $matches)) {
            // error_log("match one yield: " . $matches[1]);
            // error_log("try to match the next yield from: " . $matches[2]);
            $numOfYields = numOfYields($matches[2]);
            if ($numOfYields) {
                return 1 + $numOfYields;
            }
        } else if (preg_match_u("/^${patternOfYield}[&|]\s*([\s\S]+)$/", $statement, $matches)) {
            // error_log("match one yield: " . $matches[1]);
            // error_log("try to match the next yield from: " . $matches[2]);
            $numOfYields = numOfYields($matches[2]);
            if ($numOfYields) {
                return $numOfYields;
            }
        }
        // error_log("match failed: " . $statement);
    }

    return 0;
}

function analyze_apply($py, &$i)
{
    // ++ $i;
    $numOfYields = 0;
    $count = count($py);
    for (; $i < $count; ++ $i) {
        $statement = $py[$i];
        if (is_def_start('prove', $statement, $matches)) {
            // error_log('prove begins: ' . $statement);
            break;
        }

        if (preg_match('/^@prove/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^from/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^ *$/', $statement, $matches)) {
            continue;
        }

        if (preg_match('/^(?:    )+return +(.+) */', $statement, $matches)) {
            if ($numOfYields)
                continue;
            // error_log('return statement: ' . $statement);
            $yield = $matches[1];
            // error_log('matches[1]=' . $yield);
            if (! strcmp($yield, 'None'))
                continue;

            do {
                $yield = rtrim($yield);
                $yield = rtrim($yield, "\\");

                $numOfYields = numOfYields($yield);
                if ($numOfYields)
                    break;

                ++ $i;
                if ($i >= $count)
                    break;
                $yield .= $py[$i];
            } while (true);
        }
    }

    return $numOfYields;
}

function detect_axiom(&$statement)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False)
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];
        // error_log('create_a_tag: ' . __LINE__);
        return [
            $theorem
        ];
    } else {
        return [];
    }
}

function detect_axiom_given_theorem(&$theorem, &$statement)
{
    if (startsWith($theorem, '.')) {
        // consider the case
        // Eq << Eq[-1].reversed.apply(discrete.sets.unequal.notcontains, evaluate=False)
        return detect_axiom($statement);
    }

    if (startsWith($theorem, 'Eq')) {
        // consider the case
        // Eq[-2].this.args[0].apply(algebre.condition.condition.imply.et, invert=True, swap=True)
        return detect_axiom($statement);
    }

    if (strpos($theorem, 'Eq.') === false) {
        return [
            $theorem
        ];
    }

    return detect_axiom($statement);
}

// input is a py file
function yield_from_py($python_file)
{
    assert(file_exists($python_file), "file_exists($python_file)");

    $inputs = [];
    $input = [];

    $axiom_prefix = [];
    $py = file($python_file);
    for ($i = 0; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        // from axiom.keras import bilinear # python import statement
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

                array_push($namespaces, ...$namespaces_addition);

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

        // $yield = [
        // 'line' => $i
        // ];

        if (is_def_start('apply', $statement, $matches)) {
            yield [
                'axiom_prefix' => $axiom_prefix,
                'line' => $i
            ];

            // error_log('given begins: ' . $statement);
            $numOfYields = analyze_apply($py, $i);
            // error_log('given ended: ' . $statement);
            yield [
                'numOfYields' => $numOfYields,
                'line' => $i + 1
            ];

            break;
        }
    }

    // error_log('axiom_prefix: ' . jsonify($axiom_prefix));
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

        $yield = [
            'statement' => $statement,
            'line' => $i
        ];

        global $balancedParanthesis;
        // Eq <<= geometry.plane.trigonometry.sine.principle.add.apply(*Eq[-2].rhs.arg.args), geometry.plane.trigonometry.cosine.principle.add.apply(*Eq[-1].rhs.arg.args)
        if (preg_match_u("/((?:Eq *<<= *|Eq\.\w+, *Eq\.\w+ *= *)([\w.]+|Eq[-\w.\[\]]*\[-?\d+\][\w.]*)\.apply$balancedParanthesis\s*[,&]\s*)(.+)/", $statement, $matches)) {
            // error_log('theorem detected: ' . $theorem);
            $first_statement = $matches[1];
            $a = detect_axiom_given_theorem($matches[2], $first_statement);

            $second_statement = $matches[3];
            if (strcmp($second_statement, "\\")) {
                preg_match_u("/([\w.]+|Eq[-\w.\[\]]*\[-?\d+\])\.apply\(/", $second_statement, $matches);

                $second = detect_axiom_given_theorem($matches[1], $second_statement);
                if (count($second)) {
                    array_push($a, ...$second);
                    $yield['pivot'] = strlen($first_statement);
                }
            }

            $yield['a'] = $a;
        } else if (preg_match_u("/([\w.]+)\.apply\(/", $statement, $matches)) {
            // error_log('theorem detected: ' . $theorem);
            $a = detect_axiom_given_theorem($matches[1], $statement);

            if (count($a)) {
                $yield['a'] = $a;
            }
        } else if (preg_match('/(=|<<) *apply\(/', $statement, $matches)) {
            // error_log('yield statement: ' . $statement);
            // error_log("php = $php");
            $yield['module'] = to_python_module($python_file);
        } else {
//             error_log("statement = $statement");
            $a = detect_axiom($statement);

            if (count($a)) {
                $yield['a'] = $a;
            }
        }
        yield $yield;
    }
}

// global variables:
$sagemath = basename(dirname(dirname(__file__)));

$balancedParanthesis = balancedParentheses(7);
$balancedBrackets = balancedBrackets(4);
$patternOfYield = "(?:((?:\w+\.)*\w+)\s*(?:$balancedBrackets\s*)?$balancedParanthesis|\w+(?:\.\w+)*)\s*";

function preg_match_u($regex, $str, &$matches)
{
    return preg_match($regex . "u", $str, $matches);
}

?>
