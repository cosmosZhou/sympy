<?php
require_once '../utility.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

$folder = $dict['folder'];

$packages = [];

$folder = dirname(dirname(dirname(__file__))).'/axiom'.$folder;

foreach (scandir($folder) as $file) {
    switch ($file) {
        case ".":
        case "..":
        case "__pycache__":
            break;
        case "__init__.py":
            break;
        default:
            if (!\std\endsWith($file, '.py')) {
                $packages[] = $file;
            }
    }
}

echo \std\jsonify($packages);

?>