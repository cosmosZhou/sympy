<?php
include_once 'index.html';
require_once 'utility.php';
?>
the whole math theory is composed of the following sections:

<form style="float: right" name=search enctype="multipart/form-data"
	method="post" action="search.php">
	<input type=text spellcheck=false name=keyword size="48" value=""
		placeholder='input a hint for search of a theorem/axiom'><br> <input
		type=checkbox name=CaseSensitive><u>C</u>ase sensitive <input
		type=checkbox name=WholeWord><u>W</u>hole word <input type=checkbox
		name=RegularExpression>Regular e<u>x</u>pression
</form>
<br>
<?php

function yield_empty_directory($dir)
{
    $empty = true;
    foreach (read_files($dir, 'py') as $py) {
        if (! strcmp(basename($py), '__init__.py')) {
            continue;
        }

        $empty = false;
    }

    foreach (read_directory($dir) as $directory) {
        if (! strcmp(basename($directory), '__pycache__')) {
            continue;
        }

        $array = iterator_to_array(yield_empty_directory($directory));
        if (empty($array)) {
            $empty = false;
        } else {
            if (strcmp(end($array), $directory)) {
                $empty = false;
            }
            // is not empty;
            foreach ($array as $directory) {
                yield $directory;
            }
        }
    }

    if ($empty)
        yield $dir;
}

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
            if ($trim) {
                $buffer = trim($buffer);
                if (empty($buffer)) {
                    continue;
                }
            }

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
        if (is_latex($statement, $matches)) {
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
    // https://www.php.net/manual/en/function.substr.php
    $py = substr($php, 0, - 3) . 'py';
    if (! file_exists($py)) {
        echo "$php is an obsolete file since its py file is deleted!<br>";
        // if error of Permission denied ocurrs, run the following command:
        // chmod -R 777 axiom
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

foreach (yield_empty_directory(dirname(__file__)) as $directory) {
    echo "$directory is an obsolete folder since there is no py file in it!<br>";
    // if error of Permission denied ocurrs, run the following command:
    // chmod -R 777 axiom
    removedir($directory);
}

echo "in summary:<br>";
echo "there are $count axioms in all, wherein:<br>";
echo "${tab}there are " . accumulate($plausible) . " axioms plausible;<br>";
echo "${tab}there are " . accumulate($unprovable) . " axioms unprovable;<br>";
echo "${tab}there are " . accumulate($insurmountable) . " axioms insurmountable.<br>";

?>

<script>
	$("input[type=text]")[0].focus();
</script>
