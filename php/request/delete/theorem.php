<?php
require_once '../../utility.php';
require_once '../../mysql.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'package::',
        'theorem::'
    ]);
}

$package = $dict['package'];
$theorem = $dict['theorem'];

error_log("package = $package");
error_log("theorem = $theorem");

$module = "$package.$theorem";
$py = module_to_py($module);
error_log("py = $py");

if (\std\endsWith($py, "/__init__.py")) {
    $init = new Text($py);
    $lines = $init->preg_match('^from . import \w+');
    $init->writelines($lines);

    \mysql\delete_from_suggest($module, true);
} else {
    unlink($py);
    delete_from_init($package, $theorem);

    \mysql\delete_from_suggest($module);
}

\mysql\delete_from_axiom($module);
echo \std\jsonify("deleted!");
?>