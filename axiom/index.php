<?php
include_once 'index.html';
require_once 'utility.php';
?>
the whole math theory is composed of the following sections:
<br>
<?php

function read_all_php($dir)
{
    foreach (read_directory($dir) as $directory) {
        foreach (read_all_files($directory, 'php') as $php) {
            yield $php;
        }
    }
}

function read_from($file, $trim = true)
{
    if (file_exists($file)) {

        $handle = fopen($file, "r");

        while (($buffer = fgets($handle, 4096)) !== false) {
            if ($trim)
                yield trim($buffer);
            else
                yield $buffer;
        }

        if (! feof($handle)) {
            echo "Error: unexpected fgets() fail\n";
        }

        fclose($handle);
    }
}

function is_axiom_plausible($php)
{
    foreach (yield_from_php($php) as &$statement) {
        if (preg_match_all('/\\\\[(].+?\\\\[)]/', $statement, $matches, PREG_SET_ORDER)) {
            foreach ($matches as list ($match)) {
                if (preg_match("/.+tag\*\{(.+=>.+)\}.+/", $match, $result)) {
                    return true;
                }
            }
        }
    }
    return false;
}

function accumulate($dict)
{
    $sum = 0;
    foreach ($dict as $key => $value) {
        $sum += count($value);
    }
    return $sum;
}

global $sagemath;

$unprovable = [];
$insurmountable = [];
$plausible = [];

function section($axiom)
{
    list (, $section,) = explode('.', $axiom, 3);
    return $section;
}

foreach (read_from(dirname(__file__) . '/insurmountable.txt') as $axiom) {
    $insurmountable[section($axiom)][] = $axiom;
}

foreach (read_from(dirname(__file__) . '/unprovable.txt') as $axiom) {
    $unprovable[section($axiom)][] = $axiom;
}

$count = 0;
foreach (read_all_php(dirname(__file__)) as $php) {
//     https://www.php.net/manual/en/function.substr.php
    $py = substr($php, 0, -3).'py';
    if (!file_exists($py)) {
        echo "$php is an obsolete file since its py file is deleted!<br>";
        unlink($php);
        continue;
    }
    
    ++ $count;
    if (is_axiom_plausible($php)) {
        $axiom = to_python_module($php);

        $section = section($axiom);
        if (array_key_exists($section, $insurmountable)) {
            if (in_array($axiom, $insurmountable[$section]))
                continue;
        }

        if (array_key_exists($section, $unprovable)) {
            if (in_array($axiom, $unprovable[$section]))
                continue;
        }
        // echo $axiom . " is plausible<br>";

        $plausible[$section][] = $axiom;
    }
}

$tab = str_repeat("&nbsp;", 8);
foreach (read_directory(dirname(__file__)) as $directory) {
    $section = basename($directory);
    if (! strcmp($section, '__pycache__')) {
        continue;
    }

    echo "$tab<a href=$section>$section</a><br>";

    if (array_key_exists($section, $insurmountable)) {
        echo "$tab${tab}<font color=blue>axioms insurmountable:</font><br>";
        foreach ($insurmountable[$section] as $axiom) {
            echo "$tab$tab$tab" . to_a_tag($axiom) . "<br>";
        }
    }
    if (array_key_exists($section, $unprovable)) {
        echo "$tab${tab}<font color=green>axioms unprovable:</font><br>";
        foreach ($unprovable[$section] as $axiom) {
            echo "$tab$tab$tab" . to_a_tag($axiom) . "<br>";
        }
    }
    if (array_key_exists($section, $plausible)) {
        echo "$tab${tab}<font color=red>axioms plausible:</font><br>";
        foreach ($plausible[$section] as $axiom) {
            echo "$tab$tab$tab" . to_a_tag($axiom) . "<br>";
        }
    }
}

echo "in summary:<br>";
echo "there are $count axioms in all, wherein:<br>";
echo "${tab}there are " . accumulate($plausible) . " axioms plausible;<br>";
echo "${tab}there are " . accumulate($unprovable) . " axioms unprovable;<br>";
echo "${tab}there are " . accumulate($insurmountable) . " axioms insurmountable.<br>";

?>