<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';

function piece_together(&$input)
{
    $code = implode("\n", $input);
    $input = null;
    return $code;
}

if (array_key_exists("PATH_INFO", $_SERVER)) {
    $PATH_INFO = $_SERVER["PATH_INFO"];
    if (\std\equals($PATH_INFO, '/')) {
        $PATH_INFO = null;
    }
} else {
    $PATH_INFO = null;
}

if (! $PATH_INFO) {
    require_once 'php/summary.php';
    die();
}

error_log("PATH_INFO = $PATH_INFO");
// \std\println("PATH_INFO = $PATH_INFO");

$path_info = substr(__FILE__, 0, - 4) . $PATH_INFO;

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
                $base_init = new \std\Text($base_init);

                $moduleName = substr(basename($py), 0, - 3);

                $base_init->append("\n\nfrom . import $moduleName");
            }

            if (file_exists($py)) {
                die("$py already exists!");
            }

            $file = new \std\Text($py);
            $code = "from util import *\n\n\n";

            $code .= $applyCodes . "\n";
            foreach (explode("\n", $proveCodes) as $line) {
                $code .= "    $line\n";
            }

            $code .= "\n\nif __name__ == '__main__':\n";
            $code .= "    run()";

            $file->write($code);

            insert_into_init($py);
        }

        list ($logs, $sql_statement, $statementsFromSQLFile) = run($py);

        error_log("logs = " . \std\jsonify($logs));
        error_log("sql_statement = $sql_statement");
        error_log("statementsFromSQLFile = " . \std\jsonify($statementsFromSQLFile));
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
            if ($input == null && end($inputs)[- 1] == '\\') {
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
require_once $indexOfYield < 0 ? 'php/folderView.php' : 'php/render.php';
?>

