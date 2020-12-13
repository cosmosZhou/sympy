<?php
include_once 'index.html';
// include_once dirname(dirname(__FILE__)) . '/index.html';

// use the following regex to remove error_log prints:^ +error_log
// to speed up the .php page rendering, disable error_log!!
$sagemath = basename(dirname(dirname(__file__)));

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
?>
