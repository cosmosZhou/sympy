<?php
// if (! defined('SAGEMATH_ROOT')) {
// define('SAGEMATH_ROOT', dirname(dirname(__FILE__)) . '/');
// }
include_once 'index.html';
require_once 'utility.php';

// ^ +error_log
// include_once dirname(dirname(__FILE__)) . '/index.html';
function str_html($param)
{
    // preg_replace()
    return preg_replace("/<(?=[a-zA-Z!\/])/", "&lt;", str_replace("&", "&amp;", $param));
}

function replace_white_spaces($param)
{
    return str_replace(" ", "&nbsp;", $param);
}

// use the following regex to remove error_log prints:^ +error_log
// to speed up the .php page rendering, disable error_log!!

global $sagemath;

function create_text_tag(&$statement)
{
    $length = strlen($statement) + 2;
    $statement_quote = quote($statement);
    return "<input spellcheck=false name=python[] size=$length value='$statement_quote'>";
}

function create_a_tag_with_this_module(&$statement, $module)
{
    $length = strlen($statement);
    $statement_quote = quote($statement);
    global $sagemath;
    $request_url = "/$sagemath/axiom/request.php?callee=$module";
    return "<a href='$request_url'>$statement_quote</a>";
}

function create_a_tag($theorem, &$statement, &$axiom_prefix)
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

    $theorem = str_replace(".", "/", $theorem);
    global $sagemath;
    if (strlen($head)) {
        $prefix = $axiom_prefix[$head];
        $full_theorem_path = "/$sagemath/$prefix";
    } else
        $full_theorem_path = "/$sagemath";

    $full_theorem_path .= "/$theorem.php";

    $statement_quote = str_html($statement);
    $statement_quote = replace_white_spaces($statement_quote);

    return "<a href='$full_theorem_path'>$statement_quote</a>";
}

// input is a php file
function render($php)
{
    // error_log("php file = $php");
    $py = str_replace('.php', '.py', $php);
    // $py = str_replace('latex', 'sympy', $py);
    // error_log("python file = $py");

    assert(file_exists($py), "file_exists($py)");

    $lengths = [];

    $indexOfYield = - 1;
    $counterOfLengths = 0;

    $inputs = [];
    $input = [];

    foreach (yield_from_py($py) as $dict) {
        // error_log(jsonify($dict));

        if (array_key_exists('axiom_prefix', $dict)) {
            $axiom_prefix = $dict['axiom_prefix'];
            continue;
        }

        if (array_key_exists('numOfYields', $dict)) {
            $numOfYields = $dict['numOfYields'];
            continue;
        }

        if (array_key_exists('given', $dict)) {
            $given = $dict['given'];
            if (! strcmp($given, "True")) {
                $given = "imply";
                $imply = "given";
                continue;
            }
        }

        if (array_key_exists('imply', $dict)) {
            $imply = $dict['imply'];
            if (! strcmp($imply, "True")) {
                $given = "given";
                $imply = "imply";
                continue;
            }
        }

        $statement = $dict['statement'];

        if (array_key_exists('pivot', $dict)) {
//            error_log("dict: " . jsonify($dict));
            $pivot = $dict['pivot'];
            $a = $dict['a'];
            $first_statement = substr($statement, 0, $pivot);
            $second_statement = substr($statement, $pivot);
            $html = create_a_tag($a[0], $first_statement, $axiom_prefix);
            
            if ($a[1] == null) {
                $html .= create_text_tag($second_statement);
            } else {
                $html .= create_a_tag($a[1], $second_statement, $axiom_prefix);
            }
            $input[] = $html;
        } else if (array_key_exists('module', $dict)) {
            $module = $dict['module'];
            $indexOfYield = $counterOfLengths;
            $input[] = create_a_tag_with_this_module($statement, $module);
        } else if (array_key_exists('a', $dict)) {
            $a = $dict['a'][0];
            $a = create_a_tag($a, $statement, $axiom_prefix);
            if (startsWith($statement, '    '))
                $inputs[count($inputs) - 1] .= "<br>$a";
            else
                $input[] = $a;
        } else {
            $text = create_text_tag($statement);

            // error_log("create_text_tag: " . $statement);
            if (startsWith($statement, '    ') && $input == null) {
                // starting with more than 4 spaces indicates this line is a continuation of the previous line of code!
                $inputs[count($inputs) - 1] .= "<br>$text";
            } else {
                $input[] = $text;
            }
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            $inputs[] = join("<br>", $input);
            $input = null;
            // unset($input);

            ++ $counterOfLengths;
            $lengths[] = 1;
        } else if (preg_match_u('/(Eq\.\w+ *(?:, *(?:Eq\.\w+|\w+|\*\w+) *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            // error_log("parameter: " . $statement);

            // https://www.php.net/manual/en/function.preg-match-all.php
            preg_match_all('/Eq\.\w+/u', $statement, $matches, PREG_SET_ORDER);

            ++ $counterOfLengths;
            $lengths[] = count($matches);

            $inputs[] = join("<br>", $input);
            unset($input);
        }
    }

    echo "<h3><font color=blue>$given:</font></h3>";
    // error_log("indexOfYield = $indexOfYield");

    $numOfReturnsFromApply = $lengths[$indexOfYield];
    // error_log("numOfReturnsFromApply = " . $numOfReturnsFromApply);

    // error_log("lengths = " . jsonify($lengths));

    $p = [];
    $i = 0;
    $statements = '';
    $statements_before_yield = '';
    foreach (yield_from_php($php) as &$statement) {

        if ($i == $indexOfYield) {

            // error_log($statement);
            -- $lengths[$i];
            $statements .= $statement;
            if ($lengths[$i] == 0) {

                if ($numOfReturnsFromApply == 1) {
                    if (is_latex($statement, $matches)) {
                        // error_log("matches = ".jsonify($matches));
                        $numOfReturnsFromApply = count($matches);
                        // error_log("count(matches) = ".$numOfReturnsFromApply);

                        $statements_before_yield = array_slice($matches, 0, $numOfReturnsFromApply - $numOfYields);
                        // error_log("statements_before_yield = ".jsonify($statements_before_yield));
                        $statements = array_slice($matches, $numOfReturnsFromApply - $numOfYields);
                        // error_log("statements_after_yield = ".jsonify($statements));

                        foreach ($statements as &$statement) {
                            $statement = $statement[0];
                        }
                        $statements = join('', $statements);

                        foreach ($statements_before_yield as &$statement) {
                            $statement = $statement[0];
                        }
                        $statements_before_yield = join('', $statements_before_yield);
                    }
                }

                $p[] = "<p>$statements_before_yield</p><h3><font color=blue>$imply:</font></h3><p>$statements</p><h3><font color=blue>prove:</font></h3>";

                $statements = '';
                $statements_before_yield = '';
                ++ $i;
            } else if ($lengths[$i] == $numOfYields) {
                $statements_before_yield = $statements;
                // error_log("lengths[i] = ".$lengths[$i]);
                // error_log("statements_before_yield = $statements_before_yield");

                $statements = '';
            }
        } else {
            $statements .= $statement;
            -- $lengths[$i];
            if ($lengths[$i] == 0) {
                $p[] = "<p>$statements</p>";
                $statements = '';
                ++ $i;
            }
        }
    }

    $size = min(count($inputs), count($p));
    for ($i = 0; $i < $size; ++ $i) {
        echo $inputs[$i];
        $statement = $p[$i];
        echo $statement;
    }
}
?>
