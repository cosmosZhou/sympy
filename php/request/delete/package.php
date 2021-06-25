<?php
require_once '../../utility.php';
require_once '../../mysql.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'section::',
        'package::'
    ]);
}

$package = $dict['package'];
$section = $dict['section'];

error_log("package = $package");
error_log("section = $section");

$path = module_to_path("$section.$package");

error_log("path = $path");
$initPath = "$path/__init__.py";
$init = new Text($initPath);
if ($init->search('^@apply\b')) {

    foreach (scandir($path) as $file) {
        switch ($file) {
            case ".":
            case "..":
                break;
            case "__init__.py":
                break;
            default:
                $file = "$path/$file";
                if (is_dir($file)) {
                    \std\deleteDirectory($file);
                } else {
                    unlink($file);
                }
        }
    }

    rename($initPath, "$path.py");

    \mysql\delete_from_suggest($module, true);
    
    \mysql\delete_from_axiom("$module\..+", true);
} else {
    \std\deleteDirectory($path);
    delete_from_init($section, $package);

    \mysql\delete_from_suggest($module);
    
    \mysql\delete_from_axiom('$module\b', true);
}



echo \std\jsonify("deleted!");
?>