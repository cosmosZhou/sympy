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
    
    $dict['old'] = "keras.eq_cup.imply.eq.matmul.softmax.batch_gather";
    $dict['new'] = "keras.eq_card.subset_cup.imply.eq.matmul.softmax.batch_gather";
}

$old = $dict['old'];
$new = $dict['new'];

error_log("old = $old");
error_log("new = $new");

$oldPy = module_to_py($old);
$newPy = module_to_py($new);

if (! \std\endsWith($newPy, "/__init__.py")) {
    if (filesize($newPy)){
        die("$newPy already exists");
    }
    else{
        unlink($newPy);
    }
}

error_log("oldPy = $oldPy");

if (file_exists($newPy)) {
    error_log("newPy = $newPy");
    
    if (\std\endsWith($oldPy, "/__init__.py")) {
        $__init__ = new Text($oldPy);

        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
    } else {
        $newPy = new Text($newPy);
        $oldPyText = new Text($oldPy);
        $newPy->insert(0, $oldPyText->readlines());

        error_log("deleting $oldPy");
        if (!unlink($oldPy)){
            error_log("Error in deleting $oldPy");            
        }

        delete_from_init($old);
    }
    insert_into_init($new);
} else {
    $newPy = substr($newPy, 0, - strlen("/__init__.py")) . ".py";
    error_log("newPy = $newPy");
    
    \std\createDirectory(dirname($newPy));

    if (\std\endsWith($oldPy, "/__init__.py")) {
        $__init__ = new Text($oldPy);
        
        $newPyText = new Text($newPy);
        $newPyText->writelines($__init__->retain('^from \. import \w+'));
        insert_into_init($new);
    } else {
        
        $substr = substr($new, 0, strrpos($new, '.'));        
        $substrPy = module_to_py($substr);
        if (! \std\endsWith($substrPy, "/__init__.py")) {
            $substrPyInit = substr($substrPy, 0, -3) . "/__init__.py";
            if (dirname($substrPyInit).".py" == $oldPy){
                $__init__ = new Text($substrPyInit);
                $newPackages = explode('.', $new);
                $newPackageLast = end($newPackages);
                $__init__->write("from . import $newPackageLast");
            }
            else{
                if (! rename($substrPy, $substrPyInit)) {
                    die("failed in renameing $substrPy to $substrPyInit");
                }
            }
        }
        
        error_log("renaming from $oldPy to $newPy");
        if (! rename($oldPy, $newPy)) {
            die("failed in renameing $oldPy to $newPy");
        }

        delete_from_init($old);
        insert_into_init($new);
    }
}

\mysql\delete_from_suggest($old);
\mysql\insert_into_suggest($new);

\mysql\update_axiom($old, $new);
\mysql\update_hierarchy($old, $new);

echo \std\jsonify("renamed!");
?>