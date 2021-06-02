<?php
require_once '../../utility.php';
require_once '../../mysql.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

$user = $dict['user'];
$package = $dict['package'];
$theorem = $dict['theorem'];

error_log("user = $user");
error_log("package = $package");
error_log("theorem = $theorem");

if (! \std\endsWith($package, '/')) {
    $package .= '/';
}

$ROOT = $_SERVER['DOCUMENT_ROOT'];
$folder = $ROOT . "/" . $user . "/axiom/" . $package;
error_log("folder = $folder");
error_log("package = $package");
error_log("theorem = $theorem");

$py = $folder . "/$theorem.py";
if (file_exists($py)) {
    unlink($py);
}

delete_from_init($folder, $theorem);
?>