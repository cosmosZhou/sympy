<?php
include_once 'index.html';

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

function str_html($param)
{
    // preg_replace()
    return preg_replace("/<(?=[a-zA-Z!\/])/", "&lt;", str_replace("&", "&amp;", $param));
}

function create_html_tag(&$statement, &$axiom_prefix)
{
    // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False):
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];

        return create_a_tag($theorem, $statement, $axiom_prefix);
    } else {
        return create_text_tag($statement);
    }
}

function create_text_tag(&$statement)
{
    $length = strlen($statement);
    $statement_quote = quote($statement);
    return "<input name=python[] size = $length value = '$statement_quote'>";
}

function create_a_tag($theorem, &$statement, &$axiom_prefix)
{
    $dot_index = strpos($theorem, '.');
    if ($dot_index === false) {
        $head = $theorem;
    } else {
        $head = substr($theorem, 0, $dot_index);
    }

    $theorem = str_replace(".", "/", $theorem);

    $prefix = $axiom_prefix[$head];
    if ($prefix)
        $full_theorem_path = '/sympy/' . $prefix;
    else
        $full_theorem_path = '/sympy';

    $full_theorem_path .= '/' . $theorem . '.php';

    error_log('full_theorem_path = ' . $full_theorem_path);

    $statement_quote = str_html($statement);
    return "<a name=python[] href='$full_theorem_path'>$statement_quote</a>";
}

// input is a php file
function render($php, $txt)
{
    // error_log("php file = $php");
    // $txt = str_replace('.php', '.txt', $php);
    // error_log("txt file = $txt");
    $py = str_replace('.php', '.py', $php);
    // $py = str_replace('latex', 'sympy', $py);
    // error_log("python file = $py");

    // assert(file_exists($txt), "file_exists($txt)");
    assert(file_exists($py), "file_exists($py)");

    $inputs = [];
    $input = [];

    $axiom_prefix = [];
    $py = file($py);
    for ($i = 0; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        // from axiom.neuron import bilinear # python import statement
        if (preg_match('/^from +(.+) +import +(.*)/', $statement, $matches)) {

            $prefix = $matches[1];
            $namespaces = $matches[2];
            $namespaces = preg_split("/[\s,]+/", $namespaces, - 1, PREG_SPLIT_NO_EMPTY);

//             error_log("end(namespaces) = " . end($namespaces));
            if (!strcmp(end($namespaces), '\\')) {
//                 error_log("strcmp = " . strcmp(end($namespaces), '\\'));
                array_pop($namespaces);

                $statement = $py[++ $i];
//                 error_log("$statement");

                $namespaces_addition = preg_split("/[\s,]+/", $statement, - 1, PREG_SPLIT_NO_EMPTY);
//                 error_log("namespaces_addition = " . json_encode($namespaces_addition, JSON_UNESCAPED_UNICODE));

                $namespaces = array_merge($namespaces, $namespaces_addition);

//                 error_log("namespaces = " . json_encode($namespaces, JSON_UNESCAPED_UNICODE));
            }

            $prefix_path = str_replace(".", "/", $prefix);

            foreach ($namespaces as $namespace) {
                error_log('prefix detected: ' . $prefix . '.' . $namespace);
                $axiom_prefix[$namespace] = $prefix_path;
            }

            continue;
        }

        if (preg_match('/^import +(.+)/', $statement, $matches)) {
            error_log('import statement: ' . $statement);
            $packages = $matches[1];
            $packages = preg_split("/\s*,\s*/", $packages, - 1, PREG_SPLIT_NO_EMPTY);

            foreach ($packages as $package) {
                $package = preg_split("/\s+/", $package, - 1, PREG_SPLIT_NO_EMPTY);
                error_log('count(package) = ' . count($package));

                switch (count($package)) {
                    case 1:
                        $package = $package[0];
                        $axiom_prefix[$package] = '';
                        break;
                    case 2:
                        error_log('count(package[0]) = ' . $package[0]);
                        error_log('count(package[1]) = ' . $package[1]);
                        break;
                    case 3:
                        error_log('count(package[0]) = ' . $package[0]);
                        error_log('count(package[1]) = ' . $package[1]);
                        error_log('count(package[2]) = ' . $package[2]);
                        $axiom_prefix[end($package)] = '';
                        error_log('package detected: ' . $package[0]);
                        break;
                    default:
                        break;
                }
            }

            continue;
        }

        if (preg_match('/^def *prove\(Eq(, \w+)?\) *: */', $statement, $matches)) {
            break;
        }
    }

    error_log('axiom_prefix: ' . json_encode($axiom_prefix, JSON_UNESCAPED_UNICODE));

    $lengths = [];

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
            error_log('theorem detected: ' . $theorem);

            if (strpos($theorem, 'Eq.') === false) {
                $input[] = create_a_tag($theorem, $statement, $axiom_prefix);
            } else {
                $input[] = create_html_tag($statement, $axiom_prefix);
            }
        } else {
            $input[] = create_html_tag($statement, $axiom_prefix);
        }

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            $inputs[] = join(";", $input);
            unset($input);
            $lengths[] = 1;
        } else if (preg_match('/(Eq\.\w+ *(?:, *Eq\.\w+ *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            error_log("parameter: " . $statement);

            preg_match_all('/Eq\.\w+/', $statement, $matches, PREG_SET_ORDER);

            $lengths[] = count($matches);

            $inputs[] = join(";", $input);
            unset($input);
        } else {
            // error_log("python statements: $statement");
        }
        // error_log('$lengths = '.json_encode($lengths));
    }

    $p = [];
    $i = 0;
    $statements = '';
    foreach ($txt as &$statement) {
        $statements .= $statement;
        if ($lengths[$i] == 1) {
            $p[] = "<p>$statements</p>";
            $statements = '';
            ++ $i;
        } else {
            -- $lengths[$i];
        }
    }

    $size = min(count($inputs), count($p));
    for ($i = 0; $i < $size; ++ $i) {
        echo $inputs[$i];
        $statement = $p[$i];
        // if ($json) {
        // // https://www.php.net/manual/en/function.preg-match-all.php
        // if (preg_match_all('/\\\tag\*\{(Eq\[(\d+)\])\}/', $statement, $matches, PREG_SET_ORDER) || preg_match_all('/\\\tag\*\{(Eq\.(\w+))\}/', $statement, $matches, PREG_SET_ORDER)) {

        // foreach ($matches as &$match) {
        // $index = $match[2];
        // if (array_key_exists($index, $json)) {

        // $statement = str_replace("$match[1]", "$json[$index]=>$match[1]", $statement);
        // }
        // }
        // }
        // }
        echo $statement;
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

function println($param, $file = null)
{
    if (is_array($param)) {
        $param = json_encode($param, JSON_UNESCAPED_UNICODE);
    }

    if ($file) {
        echo "called in $file:<br>";
    }
    print_r($param);
    print_r("<br>");
}

?>
