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

    return "'$param'";
}

// input is a php file
function render($php)
{
    // error_log("php file = $php");
    $txt = str_replace('.php', '.txt', $php);
    // error_log("txt file = $txt");

    $py = str_replace('.php', '.py', $php);
//     $py = str_replace('latex', 'sympy', $py);
    // error_log("python file = $py");

    assert(file_exists($txt), "file_exists($txt)");
    assert(file_exists($py), "file_exists($py)");

    $inputs = [];
    $input = [];

    $py = file($py);
    for ($i = 0; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        if (preg_match('/^def *prove\(Eq\) *: */', $statement, $matches)) {
            break;
        }
    }

    $lengths = [];
    for (++ $i; $i < count($py); ++ $i) {
        $statement = $py[$i];
        // error_log("$statement");
        $statement = rtrim($statement);

        if (preg_match('/^\s*#.*/', $statement, $matches) || ! $statement) {
            continue;
        }

        if (! startsWith($statement, '    ')) {
            break;
        }

        $statement = substr($statement, 4);
        $length = strlen($statement);
        $statement_quote = quote($statement);
        $input[] = "<input name=python[] size = $length value = $statement_quote>";

        if (preg_match('/Eq *<< */', $statement, $matches)) {
            $inputs[] = join(" ", $input);
            unset($input);
            $lengths[] = 1;
        } else if (preg_match('/(Eq\.\w+ *(?:, *Eq\.\w+ *)*)= */', $statement, $matches)) {
            $statement = $matches[1];
            error_log($statement);

            preg_match_all('/Eq\.\w+/', $statement, $matches, PREG_SET_ORDER);

            $lengths[] = count($matches);

            $inputs[] = join(" ", $input);
            unset($input);
        } else {
            // error_log("python statements: $statement");
        }
        // error_log('$lengths = '.json_encode($lengths));
    }

    $p = [];
    $i = 0;
    $statements = '';
    foreach (file($txt) as &$statement) {
        $statements .= $statement;
        if ($lengths[$i] == 1) {
            $p[] = ":<p>$statements</p>";
            $statements = '';
            ++ $i;
        } else {
            -- $lengths[$i];
        }
    }

    $json = str_replace('.php', '.json', $php);

    if (file_exists($json)) {
        $json = json_decode(file_get_contents($json), true);
        foreach ($json as $key => &$value) {
            $value = reference($value);
        }
    } else {
        $json = null;
    }

    $size = min(count($inputs), count($p));
    for ($i = 0; $i < $size; ++ $i) {
        echo $inputs[$i];
        $statement = $p[$i];
        if ($json) {
            // https://www.php.net/manual/en/function.preg-match-all.php
            if (preg_match_all('/\\\tag\*\{(Eq\[(\d+)\])\}/', $statement, $matches, PREG_SET_ORDER) || preg_match_all('/\\\tag\*\{(Eq\.(\w+))\}/', $statement, $matches, PREG_SET_ORDER)) {

                foreach ($matches as &$match) {
                    $index = $match[2];
                    if (array_key_exists($index, $json)) {

                        $statement = str_replace("$match[1]", "$json[$index]=>$match[1]", $statement);
                    }
                }
            }
        }
        echo $statement;
    }

    if ($json) {
//         println("plausibles: " . json_encode($json));
        $json = array_keys($json);
        foreach ($json as &$key) {
            $key = reference($key);
        }
        println("plausibles: " . json_encode($json));
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
