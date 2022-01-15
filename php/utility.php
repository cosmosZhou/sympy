<?php
// use the following regex to remove error_log prints:
// ^ *error_log
require_once 'std.php';
use std\Set, std\Text, std\Queue;

// to speed up the .php page rendering, disable error_log!!
function py_to_module($py)
{
    $module = [];
    $pythonFile = $py;
    for (;;) {
        $dirname = dirname($pythonFile);
        $basename = basename($pythonFile);
        if (\std\equals($basename, 'axiom')) {
            break;
        }

        $module[] = $basename;
        $pythonFile = $dirname;
    }

    $module[0] = substr($module[0], 0, - strlen(\std\get_extension($module[0])) - 1);
    $module = array_reverse($module);

    if (\std\equals(end($module), '__init__')) {
        array_pop($module);
    }

    $module = join('.', $module);
    return $module;
}

function php_to_py($php)
{
    // error_log("php file = $php");
    $py = str_replace('.php', '.py', $php);
    // $py = str_replace('latex', 'sympy', $py);
    if (! file_exists($py)) {
        $py = str_replace('.php', '/__init__.py', $php);
    }
    // error_log("python file = $py");
    assert(file_exists($py), "file_exists($py)");

    return $py;
}

function module_to_py($theorem)
{
    $full_theorem_path = module_to_path($theorem);
    $py = $full_theorem_path . ".py";
    if (! file_exists($py)) {
        $py = $full_theorem_path . '/__init__.py';
    }

    return $py;
}

function module_to_path($theorem)
{
    $theorem = str_replace(".", "/", $theorem);

    return dirname(dirname(__file__)) . "/axiom/$theorem";
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

function read_all_axioms($dir)
{
    foreach (\std\list_directory($dir) as $directory) {
        foreach (\std\list_all_files($directory, 'py') as $py) {
            if (! \std\equals(basename($py), "__init__.py")) {
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

function retrieve_all_dependency()
{
    foreach (read_all_axioms(dirname(__file__)) as list ($py, $php)) {
        $from = py_to_module($php);

        $count = [];
        foreach (detect_dependency_from_py($py) as $to) {
            if (! array_key_exists($to, $count)) {
                $count[$to] = 0;
            }

            ++ $count[$to];
        }

        yield [
            $from,
            $count
        ];
    }
}

function is_def_start($funcname, $statement, &$matches)
{
    return preg_match("/^def +$funcname\([^)]*\) *: */", $statement, $matches);
}

function analyze_apply($py, &$i)
{
    $count = count($py);
    $provability = null;
    for (; $i < $count; ++ $i) {
        $statement = $py[$i];
        if (is_def_start('prove', $statement, $matches)) {
            // error_log('prove begins: ' . $statement);
            break;
        }

        if (preg_match('/^@prove(.+)/', $statement, $matches)) {
            $kwargs = $matches[1];
            if (preg_match('/^\((.+)=(.+)\)/', $kwargs, $matches)) {
                $provability = $matches[1];
            }
            continue;
        }
    }

    return $provability;
}

function detect_axiom(&$statement)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonempty, Eq.x_j_inequality, evaluate=False)
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
    if (startsWith($theorem, '.') || startsWith($theorem, 'Eq')) {
        // consider the case
        // Eq[-2].this.args[0].apply(algebra.cond.cond.imply.et, invert=True, swap=True)
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
    $inputs = [];
    $input = [];

    $py = file($python_file);
    $count = count($py);

    for ($i = 0; $i < $count; ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        // from axiom.keras import bilinear # python import statement
        if (preg_match('/^from +(.+) +import +(.*)/', $statement, $matches)) {

            $prefix = $matches[1];
            $namespaces = $matches[2];
            $namespaces = preg_split("/[\s,]+/", $namespaces, - 1, PREG_SPLIT_NO_EMPTY);

            // error_log("end(namespaces) = " . end($namespaces));
            if (\std\equals(end($namespaces), '\\')) {
                array_pop($namespaces);

                $statement = $py[++ $i];
                // error_log("$statement");

                $namespaces_addition = preg_split("/[\s,]+/", $statement, - 1, PREG_SPLIT_NO_EMPTY);
                // error_log("namespaces_addition = " . jsonify($namespaces_addition));

                array_push($namespaces, ...$namespaces_addition);

                // error_log("namespaces = " . jsonify($namespaces));
            }

            $prefix_path = str_replace(".", "/", $prefix);
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
                        break;
                    default:
                        break;
                }
            }

            continue;
        }

        if (is_def_start('apply', $statement, $matches)) {
            yield [
                'line' => $i
            ];

            // error_log('given begins: ' . $statement);
            $provability = analyze_apply($py, $i);
            // error_log('given ended: ' . $statement);
            yield [
                'line' => $i + 1,
                'provability' => $provability
            ];

            break;
        }
    }
    ++ $i;

    if ($i < $count) {
        $statement = $py[$i];

        // error_log("first statement in prove: $statement");
        if (preg_match('/^    from axiom import (.+)/', $statement, $matches)) {
            $section = explode(", ", $matches[1]);
            $yield = [
                'line' => $i,
                'section' => $section
            ];
            yield $yield;
            ++ $i;
        }

        for (; $i < $count; ++ $i) {
            $statement = $py[$i];
            $statement = rtrim($statement);
            // skip empty lines;
            if (preg_match('/^\s*$/', $statement, $matches)) {
                continue;
            }

            // the start of the next global statement other than def prove
            if (preg_match('/^\w/', $statement, $matches)) {
                break;
            }

            // stop analyzing if return statement is encountered.
            if (preg_match('/^    return\b.*$/', $statement, $matches)) {
                // error_log($statement);
                $statement = rtrim($statement);
                $statement = substr($statement, 4);

                $yield = [
                    'line' => $i,
                    'unused' => true,
                    'statement' => $statement
                ];
                // error_log(\std\jsonify($yield));
                yield $yield;

                for (++ $i; $i < $count; ++ $i) {
                    $statement = $py[$i];

                    // error_log($statement);
                    $statement = rtrim($statement);
                    // skip empty lines;
                    if (preg_match('/^\s*$/', $statement, $matches)) {
                        continue;
                    }

                    // the start of the next global statement other than def prove
                    if (preg_match('/^\w/', $statement, $matches)) {
                        break;
                    }

                    $yield = [
                        'line' => $i,
                        'unused' => true
                    ];

                    // cope with comments starting with #
                    if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                        $yield['comment'] = true;
                        $yield['statement'] = "#" . ltrim($matches[1]);
                        // error_log(\std\jsonify($yield));
                        yield $yield;
                        continue;
                    }

                    $statement = substr($statement, 4);
                    $yield['statement'] = $statement;
                    // error_log(\std\jsonify($yield));
                    yield $yield;
                }

                break;
            }

            $yield = [
                'line' => $i
            ];

            // cope with comments starting with #
            if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                $yield['comment'] = true;
                $yield['statement'] = "#" . ltrim($matches[1]);

                // error_log(\std\jsonify($yield));
                yield $yield;
                continue;
            }

            $statement = substr($statement, 4);

            $yield['statement'] = $statement;

            if (preg_match('/(=|<<) *apply\(/', $statement, $matches)) {
                // error_log('yield statement: ' . $statement);
                // error_log("php = $php");
                
                $yield['module'] = py_to_module($python_file);
            }            
            else if (match_section($statement, $matches)) {
                $index = 0;

                $dict = [];
                foreach ($matches as $module) {
                    $module = $module[0];
                    if (\std\endsWith($module, '.apply')) {
                        $module = substr($module, 0, - 6);
                    }
                    assert(is_string($module), "module is not a string: $module, statement = $statement");
                    $index = strpos($statement, $module, $index);
                    $dict[$index] = $module;

                    $index += strlen($module);
                }
                // error_log("dict = " . jsonify($dict));
                $yield['a'] = $dict;
            }             
            // error_log(\std\jsonify($yield));
            yield $yield;
        }

        for (; $i < $count; ++ $i) {
            $statement = $py[$i];
            $statement = rtrim($statement);
            // cope with comments starting with #
            if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                if (preg_match('/(created|updated) on (\d\d\d\d-\d\d-\d\d)/', $matches[1], $matches)) {

                    $yield = [
                        'line' => $i
                    ];

                    $yield['comment'] = true;
                    $yield['statement'] = '';
                    $yield[$matches[1]] = $matches[2];
                    yield $yield;
                }
            }
        }
    }
}

function match_section($statement, &$matches)
{
    return preg_match_all('/\b(?:algebra|sets|calculus|discrete|geometry|keras|stats|patent)(?:\.\w+)+/', $statement, $matches, PREG_SET_ORDER);
}

function insert_section(&$proveCodes)
{
    $from_axiom_import = determine_section($proveCodes);
    if ($from_axiom_import != "") {
        if (is_array($proveCodes)) {
            \std\array_insert($proveCodes, 0, $from_axiom_import);
        } else {
            $proveCodes = "$from_axiom_import\n$proveCodes";
        }
    }
    return $proveCodes;
}

function determine_section($proveCodes)
{
    if (is_array($proveCodes)) {
        $proveCodes = implode("\n", $proveCodes);
    }

    $section = [];

    if (match_section($proveCodes, $matches)) {
        foreach ($matches as $module) {
            $section[] = explode(".", $module[0])[0];
        }
    }

    if (! count($section)) {
        return "";
    }

    $section = new \std\Set($section);
    $section = $section->jsonSerialize();
    $section = implode(", ", $section);
    $section = "from axiom import $section";
    return $section;
}

function replace_into_init($package, $old, $new)
{
    $folder = module_to_path($package);
    $__init__ = $folder . "/__init__.py";
    $__init__ = new Text($__init__);
    $lineNum = - 1;
    foreach ($__init__ as $line) {
        ++ $lineNum;

        if (! preg_match('/^from *. *import +(.+)/', $line, $m))
            continue;

        $theorems = preg_split('/\s*,\s*/', $m[1]);
        $index = array_search($old, $theorems);
        if ($index !== false) {
            $theorems[$index] = $new;
            $theorems = implode(', ', $theorems);

            $__init__->setitem($lineNum, "from . import $theorems");
            return;
        }
    }
}

function split_module($theorem)
{
    $index = strrpos($theorem, ".");
    $package = substr($theorem, 0, $index);
    $new = substr($theorem, $index + 1);
    return [
        $package,
        $new
    ];
}

function insert_into_init($package, $new = null)
{
    error_log("insert into $package with $new");
    if ($new === null) {
        list ($package, $new) = split_module($package);

        if (strpos($package, ".") !== false)
            insert_into_init($package);
    }

    $folder = module_to_path($package);

    $__init__ = $folder . "/__init__.py";
    $__init__ = new Text($__init__);

    foreach ($__init__ as $line) {
        if (! preg_match('/^from *. *import +(.+)/', $line, $m))
            continue;
        $theorems = preg_split('/\s*,\s*/', $m[1]);
        $index = array_search($new, $theorems);
        if ($index !== false) {
            return;
        }
    }

    if (! $__init__->isEmpty() && ! $__init__->endsWith("\n"))
        $__init__->append("");

    $__init__->append("from . import $new");
}

function delete_from_init($package, $theorem = null)
{
    if ($theorem === null) {
        list ($package, $theorem) = split_module($package);
    }

    $folder = module_to_path($package);

    error_log("package = $package, theorem = $theorem");
    $initPy = $folder . "/__init__.py";

    $lineNum = - 1;

    $imports = 0;

    $lineNumIndex = - 1;
    $content = null;
    $emptyLines = 0;

    if (file_exists($initPy))
    {
        $__init__ = new Text($initPy);
        foreach ($__init__ as $line) {
            if (trim($line) == "")
                $emptyLines += 1;
            ++ $lineNum;
            if (! preg_match('/^from *. *import +(.+)/', $line, $m))
                continue;

            ++ $imports;
            $theorems = preg_split('/\s*,\s*/', $m[1]);
            error_log(\std\jsonify($theorems));

            $index = array_search($theorem, $theorems);
            if ($index !== false) {

                error_log("index = $index");

                \std\array_delete($theorems, $index);

                $theorems = implode(', ', $theorems);

                error_log("theorems = $theorems");

                if ($theorems != "") {
                    ++ $imports;
                    $content = "from . import $theorems";
                }

                $lineNumIndex = $lineNum;
            }
        }

        if ($content)
            $__init__->setitem($lineNum, $content);
        else
            $__init__->delitem($lineNumIndex);
    }

    if ($imports == 1) {
        error_log("imports = 1");
        
        error_log("folder = $folder");
        $subFolder = "$folder/$theorem";
        foreach (\std\list_all_files($folder, 'py') as list ($pyFile, $php)) {
//             if (\std\startsWith($subFolder)){
//                 error_log("detect py file $pyFile within the deleted $subFolder, so continue the process!");
//                 continue;
//             }
            
//             if (file_exists($pyFile)){
                error_log("detect py file $pyFile within the folder $folder, so cease the deleting process!");
                return;            
//             }
        }
        
        $lineNum -= $emptyLines;
        if ($lineNum > 0) {
            rename($initPy, "$folder.py");
            \std\deleteDirectory($folder);
        } else {
            \std\deleteDirectory($folder);
            delete_from_init($package);
        }
    }
    
    return;
}

// input is a py file
function modify_codes($python_file, $_proveCodes, $applyCodes = null)
{
    $proveCodes = [];
    foreach ($_proveCodes as $code) {
        $proveCodes[] = implode("\n", array_map(fn ($s) => "    $s", explode("\n", $code))) . "\n\n";
    }

    $proveCodes[] = "\n";

    $py = file($python_file);

    $count = count($py);
    if ($applyCodes === null) {
        $codes = [];
        for ($i = 0; $i < $count; ++ $i) {
            $statement = $py[$i];
            $codes[] = $statement;
            if (preg_match("/^def prove\(/", $statement, $matches)) {
                break;
            }
        }
    } else {
        $codes = [
            "from util import *\n\n\n",
            $applyCodes . "\n"
        ];

        for ($i = 0; $i < $count; ++ $i) {
            $statement = $py[$i];
            if (preg_match("/^@prove/", $statement, $matches)) {
                break;
            }
        }
    }

    for ($i; $i < $count; ++ $i) {
        if (preg_match("/^if __name__ == '__main__':/", $py[$i], $matches)) {
            break;
        }
    }

    $updatedTime = null;
    $codesAfterProve = [];
    for (; $i < $count; ++ $i) {
        $comment = $py[$i];
        if (preg_match("/ *# *(updated|created) on (\d\d\d\d-\d\d-\d\d)/i", $comment, $m)) {
            switch ($m[1]){
                case "updated":
                    $timestamp = date('Y-m-d', time());
                    $comment = "# updated on $timestamp\n";
                    $updatedTime = "$timestamp";
                    break;
                case "created":
                    $createdTime = $m[2];
                    break;
            }
        }

        $codesAfterProve[] = $comment;
    }

    if (!$updatedTime){
        $timestamp = date('Y-m-d', time());
        $updatedTime = "$timestamp";
        if ($updatedTime != $createdTime){
            $codesAfterProve[] = "# updated on $timestamp\n";            
        }
    }

    array_push($codes, ...$proveCodes, ...$codesAfterProve);

    $code = join('', $codes);
    file_put_contents($python_file, $code);
}

function read_all_php($dir)
{
    foreach (\std\list_directory($dir) as $directory) {
        foreach (\std\list_all_files($directory, 'php') as $php) {
            yield $php;
        }
    }
}

function detect_dependency_by_module($module, $unique = true)
{
    // error_log("module = " . $module);
    $py = module_to_py($module);
    // error_log("py = " . $py);

    $array = detect_dependency_from_py($py);
    if ($unique) {
        // https://www.php.net/manual/en/function.array-flip.php

        // $array = array_flip(array_flip($array));
        // $array = array_values($array);

        $set = new Set();
        $set->addAll($array);
        return $set;
    }
    return $array;
}

// input is a py file
function detect_dependency_from_py($py)
{
    $axioms = [];

    foreach (yield_from_py($py) as $dict) {
        // error_log(jsonify($dict));

        if (array_key_exists('a', $dict)) {
            foreach ($dict['a'] as $index => &$axiom) {
                $axioms[] = $axiom;
            }
        }
    }
    return $axioms;
}

function establish_dialetic_graph($theorem)
{
    $setProcessed = new Set();

    $G = [];
    $queue = new Queue();
    $queue->push($theorem);

    while (! $queue->isEmpty()) {
        $theorem = $queue->pop();
        if ($setProcessed->contains($theorem))
            continue;

        $setProcessed->add($theorem);

        foreach (detect_dependency_by_module($theorem) as $child) {
            $queue->push($child);
            $G[$theorem][] = $child;
        }
    }

    return $G;
}

function look_for_executable_python()
{
    switch (PHP_OS) {
        case 'Unix':
        case 'FreeBSD':
        case 'NetBSD':
        case 'OpenBSD':
        case 'Linux':
            return "python";
        case 'WINNT':

        case 'WIN32':

        case 'Windows':
            // return "D:\Users\dell\AppData\Local\Programs\Python\Python36\python.exe";
            return "\"D:\Program Files\Python\Python36\python.exe\"";
        // exec("echo %PATH%", $array, $ret);
        // $array = $array[0];
        // $array = explode(';', $array);
        // foreach ($array as $path) {
        // $path = "$path\python.exe";
        // if (file_exists($path)) {
        // return "\"$path\"";
        // }
        // }

        case 'CYGWIN_NT':

        case 'Darwin':

        case 'IRIX64':

        case 'SunOS':

        case 'HP-UX':
            return "python";
    }

    return python;
}

function run($py)
{
    $module = py_to_module($py);
    $logs[] = "module = " . str_replace(".", "/", $module);
    $user = basename(dirname(dirname(__file__)));
    if (\std\is_linux()) {
        // $array = file_get_contents("http://localhost:8000/sympy/run.py?module=$module");
        $array = file_get_contents("https://www.axiom.top/$user/run.py?module=$module");
        $array = explode("\n", $array);
    } else {
        $array = file_get_contents("http://localhost/$user/run.py?module=$module", 0, stream_context_create([
            'http' => [
                'timeout' => 3000
            ]
        ]));
        $array = explode("\r\n", $array);
    }

    $data = null;
    foreach ($array as &$line) {
//         error_log("line = " . $line);
        if (preg_match('/^b([\'"])(.+)\1$/', $line, $m)) {
            $line = $m[2];
            if ($m[1] == "'"){
                $line = str_replace('"', '\\"', $line);
                $data = explode("\v", eval("return \"$line\";"));
                $index = count($data) - 1;
                $data[$index] = str_replace("\\'", "'", $data[$index]);
            }
            else{
                $data = explode("\v", eval("return \"$line\";"));
            }
            break;
        }
        else{
            $logs[] = $line;
        }
    }

    return [
        $logs,
        $data
    ];
}

function compile_python_file($py)
{
    $text = new \std\Text($py);
    foreach ($text as $line) {
        error_log($line);
    }
    // $user = basename(dirname(dirname(__file__)));
    // if (\std\is_linux()) {
    // $url = "https://www.axiom.top:5000/compile";
    // } else {
    // $url = "http://localhost:5000/compile";
    // }

    // $data = ["py"=> $py];
    return "error detected!";
}

function fetch_codes($module, $fetch_prove = false)
{
    $py = module_to_py($module);
    $py = file($py);
    $apply = [];

    $count = count($py);
    for ($i = 1; $i < $count; ++ $i) {
        $line = $py[$i];

        $apply[] = $line;

        if (preg_match('/^def prove\(/', $line, $matches)) {
            ++ $i;
            break;
        }
    }

    $apply = trim(implode("", $apply));

    if ($fetch_prove) {
        $prove = [];
        $line = $py[$i];
        if (preg_match('/^    from axiom import \w+/', $line, $matches)) {
            ++ $i;
        }

        for (; $i < $count; ++ $i) {
            $line = $py[$i];
            if (preg_match('/^if +/', $line, $matches)) {
                break;
            }

            if (\std\startsWith($line, '    ')) {
                $line = substr($line, 4);
            }

            $prove[] = $line;
        }

        $prove = rtrim(implode("", $prove));

        return [
            $apply,
            $prove
        ];
    }

    return $apply;
}

function axiom_directory()
{
    return dirname(dirname(__file__)) . "/axiom/";
}
?>
