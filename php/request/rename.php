<?php
require_once '../utility.php';
require_once '../mysql.php';
use std\Graph, std\Text, std\Set;

global $user;

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'old::',
        'new::'
    ]);
}

$old = $dict['old'];
$new = $dict['new'];

$oldPy = module_to_py($old);
$newPy = module_to_py($new);

if (! \std\endsWith($newPy, "/__init__.py")) {
    die("$newPy already exists");
}

error_log("oldPy = $oldPy");
error_log("new = $new");

if (file_exists($newPy)) {
    if (\std\endsWith($oldPy, "/__init__.py")) {
        $__init__ = new Text($oldPy);

        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
    } else {
        $newPy = new Text($newPy);
        $oldPyText = new Text($oldPy);
        $newPy->insert(0, $oldPyText->readlines());
        
        unlink($oldPy);
        delete_from_init($old);
    }
} else {
    $newPy = substr($newPy, 0, - strlen("/__init__.py")) . ".py";

    \std\createDirectory(dirname($newPy));

    if (\std\endsWith($oldPy, "/__init__.py")) {
        $__init__ = new Text($oldPy);

        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
    } else {
        if (! rename($oldPy, $newPy)) {
            die("failed in renameing $oldPy to $newPy");
        }

        delete_from_init($old);
    }
}


insert_into_init($new);

\mysql\delete_from_suggest($old);
\mysql\insert_into_suggest($new);

\mysql\update_axiom($old, $new);
\mysql\update_hierarchy($old, $new);

echo \std\jsonify("renamed!");
?>