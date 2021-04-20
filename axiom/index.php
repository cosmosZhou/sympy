<?php
include_once 'index.html';
require_once 'utility.php';
?>
the whole math theory is composed of the following sections:
<?php
require_once 'searchBox.php';

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
                if (preg_match("/.+tag\*\{(\?=.+)\}.+/", $match, $result)) {
                    return true;
                }
            }
        }
    }
    return false;
}

function axiom_provability($py)
{
    $py = file($py);
    foreach ($py as &$statement) {
        if (preg_match("/^@prove\((\w+)=False\) *$/", $statement, $matches)) {
            return $matches[1];
        }
    }

    return "";
}

function accumulate($dict)
{
    $sum = 0;
    foreach ($dict as $key => $value) {
        $sum += count($value);
    }
    return $sum;
}

global $sympy;

$unprovable = [];
$insurmountable = [];
$plausible = [];

function section($axiom)
{
    list (, $section,) = explode('.', $axiom, 3);
    return $section;
}

$count = 0;
foreach (read_all_php(dirname(__file__)) as $php) {
    // https://www.php.net/manual/en/function.substr.php
    $path = substr($php, 0, - 3);
    $py = $path . 'py';

    if (! file_exists($py)) {
        $py = $path . '/__init__.py';
    }

    if (! file_exists($py)) {
        echo "$php is an obsolete file since its py file is deleted!<br>";
        // if error of Permission denied ocurrs, run the following command:
        // chmod -R 777 axiom
        unlink($php);
        continue;
    }

    ++ $count;
    switch (axiom_provability($py)) {
        case "surmountable":
            $axiom = to_python_module($php);
            $insurmountable[section($axiom)][] = $axiom;
            break;
        case "provable":
            $axiom = to_python_module($php);
            $unprovable[section($axiom)][] = $axiom;
            break;
        default:
            if (is_axiom_plausible($php)) {
                $axiom = to_python_module($php);

                $section = section($axiom);
                if (array_key_exists($section, $insurmountable)) {
                    if (in_array($axiom, $insurmountable[$section]))
                        break;
                }

                if (array_key_exists($section, $unprovable)) {
                    if (in_array($axiom, $unprovable[$section]))
                        break;
                }
                // echo $axiom . " is plausible<br>";

                $plausible[$section][] = $axiom;
            }
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

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="utility.js"></script>
<script>
	$("input[type=text]")[0].focus();
</script>
