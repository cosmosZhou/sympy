<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';

error_log("_GET = " . \std\jsonify($_GET));
error_log("_POST = " . \std\jsonify($_POST));

// if (! $_GET) {
// // https://www.php.net/manual/en/function.getopt.php
// $_GET = getopt("", [
// 'module::'
// ]);
// $_GET['module'] = str_replace('/', '.', $_GET['module']);
// }

$key = array_keys($_GET);
switch (count($key)) {
    case 0:
        $key = array_keys($_POST);
        switch (count($key)) {
            case 0:
                require_once 'php/summary.php';
                exit();
            default:
                if (array_key_exists('module', $_POST)) {
                    $module = $_POST['module'];
                    break;
                } else {
                    require_once 'php/search.php';
                    exit();
                }
        }
        break;
    case 1:
        list ($key) = $key;
        switch ($key) {
            case "symbol":
                require_once 'php/symbol.php';
                exit();
            case "module":
                $module = $_GET['module'];
                break;
            case "callee":
                require_once 'php/hierarchy.php';
                exit();
            case "caller":
                require_once 'php/hierarchy.php';
                exit();
            case "new":
                require_once 'php/new.php';
                exit();
            case "state":
                require_once 'php/search.php';
                exit();
        }
        break;
    case 2:
        $module = $_GET['module'];
        break;
    default:
        break;
}

function piece_together(&$input)
{
    $code = implode("\n", $input);
    $input = null;
    return $code;
}

$PATH_INFO = str_replace('.', '/', $module);

$path_info = substr(__FILE__, 0, - 4) . "/" . $PATH_INFO;

$indexOfYield = - 1;
if (! \std\endsWith($path_info, '/')) {

    $py = $path_info . ".py";

    // \std\println("py = $py");

    $statementsFromSQLFile = null;
    $sql_statement = '';

    if (! file_exists($py)) {
        $__init__ = substr($py, 0, - 3) . "/__init__.py";
        if (file_exists($__init__)) {
            $py = $__init__;
        }
    }

    $logs = [];
    $ret = 1;

    if (array_key_exists('prove', $_POST)) {
        $applyCodes = array_key_exists('apply', $_POST) ? $_POST['apply'] : null;

        $proveCodes = $_POST['prove'];

        $proveCodes = insert_section($proveCodes);
        if (is_array($proveCodes)) {
            error_log("proveCodes = " . \std\jsonify($proveCodes));

            modify_codes($py, $proveCodes, $applyCodes);
        } else {
            error_log("create new py file = $py");
            
            $base_py = dirname($py) . ".py";
            if (file_exists($base_py)) {
                $base_init = dirname($py) . "/__init__.py";
                error_log("change $base_py into $base_init");
                \std\createDirectory(dirname($py));

                rename($base_py, $base_init);
            }

            $imports = [];
            if (file_exists($py)) {
                if (! \std\endsWith($py, "/__init__.py"))
                    die("$py already exists!");
                else {
                    $file = new \std\Text($py);
                    if ($file->search('from util import \S')) {
                        die("$py already exists!");
                    }
                    $imports = $file->preg_match('from \. import');
                }
            }

            $file = new \std\Text($py);
            $code = "from util import *\n\n\n";

            $code .= $applyCodes . "\n";
            foreach (explode("\n", $proveCodes) as $line) {
                $code .= "    $line\n";
            }

            $code .= "\n\nif __name__ == '__main__':\n";
            $code .= "    run()";

            if (count($imports)) {
                $code .= "\n\n";
                $code .= implode("\n", $imports);
            }

            $file->write($code);

            insert_into_init(py_to_module($py));
        }

        list ($logs, $sql_statement, $statementsFromSQLFile) = run($py);

        error_log("logs collected from running python script:");
        foreach ($logs as &$line) {
            error_log($line);
        }

        error_log("sql_statement = $sql_statement");
        
        error_log("statementsFromSQLFile = ");
        foreach ($statementsFromSQLFile as &$line) {
            error_log($line);
        }
        
        if (! $sql_statement) {
            error_log("error detected in python file:");
            error_log("python file = $py");

            $logs[] = compile_python_file($py);
        }
    }

    $lengths = [];

    $counterOfLengths = 0;

    $inputs = [];
    $input = [];

    foreach (yield_from_py($py) as $dict) {
        // error_log("dict = " . \std\jsonify($dict));
        if (array_key_exists('numOfYields', $dict)) {
            $numOfYields = $dict['numOfYields'];
            continue;
        }

        if (! array_key_exists('statement', $dict)) {
            continue;
        }

        $statement = $dict['statement'];

        if (array_key_exists('module', $dict)) {
            $module = $dict['module'];
            $indexOfYield = $counterOfLengths;
            $input[] = $statement;
        } else if (array_key_exists('a', $dict)) {
            if (! $input && $inputs && end($inputs)[- 1] == '\\') {
                $length = count($inputs);
                $inputs[$length - 1] .= "\n$statement";
            } else {
                $input[] = $statement;
            }
        } else {
            // error_log("statement: " . $statement);
            // error_log("dict = " . \std\jsonify($dict));

            if (array_key_exists('comment', $dict)) {
                if (array_key_exists('unused', $dict))
                    $class = '"comment unused"';
                else
                    $class = "comment";
                $input[] = $statement;
                continue;
            }

            if (array_key_exists('unused', $dict)) {
                $input[] = $statement;
                continue;
            }

            $text = $statement;
            // error_log("create_text_tag: " . $statement);
            if (\std\startsWith($statement, '    ') && $input == null) {
                // starting with more than 4 spaces indicates this line is a continuation of the previous line of code!
                $inputs[count($inputs) - 1] .= "\n$text";
            } else {
                $input[] = $text;
            }
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            // error_log(jsonify($input));

            $inputs[] = piece_together($input);

            ++ $counterOfLengths;
            $lengths[] = 1;
        } else if (\std\preg_match_u('/(Eq\.\w+ *(?:, *(?:Eq\.\w+|\w+|\*\w+) *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            // error_log("parameter: " . $statement);

            // https://www.php.net/manual/en/function.preg-match-all.php
            preg_match_all('/Eq\.\w+/u', $statement, $matches, PREG_SET_ORDER);

            ++ $counterOfLengths;
            $lengths[] = count($matches);

            $inputs[] = piece_together($input);
        }
    }
}

error_log("indexOfYield = $indexOfYield");
require_once $indexOfYield < 0 ? 'php/package.php' : 'php/theorem.php';
?>

