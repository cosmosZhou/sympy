<?php
require_once '../../utility.php';
require_once '../../mysql.php';
use std\Graph, std\Text, std\Set;

global $user;

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'package::',
        'old::',
        'new::'
    ]);
    $dict['package'] = str_replace('/', '.', $dict['package']);
}

$package = $dict['package'];
$old = $dict['old'];
$new = $dict['new'];

error_log("package = $package");
error_log("old = $old");
error_log("new = $new");
$folder = axiom_directory() . str_replace('.', '/', $package) . '/';

error_log("folder = $folder");

if (strpos($new, '.') !== false) {
    error_log("found . in new!");
    $subPackages = explode('.', $new);
    $new = end($subPackages);

    $subFolder = $folder . implode("/", array_slice($subPackages, 0, - 1)) . '/';
    error_log("subFolder = $subFolder");
    \std\createDirectory($subFolder);

    if (file_exists($folder . $old . ".py")) {
        if (! file_exists($subFolder . $new . ".py")) {

            $prefix = '';
            foreach ($subPackages as $module) {
                insert_into_init("$package$prefix", $module);
                $prefix .= ".$module";
            }

            if (rename($folder . $old . ".py", $subFolder . $new . ".py")) {

                $old = "$package.$old";

                $subPackage = implode(".", array_slice($subPackages, 0, - 1));
                $new = "$package.$subPackage.$new";

                \mysql\delete_from_suggest($old);
                \mysql\insert_into_suggest($new);
                \mysql\update_axiom($old, $new);
                \mysql\update_hierarchy($old, $new);
            } else {
                die("renaming failed");
            }
        } else {
            die("$subPackage unimplemented!");
        }
    } else {
        $__init__ = $folder . $old . "/__init__.py";
        if (file_exists($__init__)) {

            $import = [];
            $statement = [];
            $text = new \std\Text($__init__);

            foreach ($text as $line) {
                if (preg_match('/from \. import +/', $line, $m))
                    $import[] = $line;
                else
                    $statement[] = $line;
            }

            if ($subPackage == $old) {
                $import[] = "from . import $new";
            }

            $text->writelines($import);

            $py = new \std\Text($subFolder . $new . ".py");
            $py->writelines($statement);

            if ($subPackage == $old) {
                $old = "$package.$old";
                $new = "$package.$subPackage.$new";

                \mysql\insert_into_suggest($new);
                \mysql\update_axiom($old, $new);
                \mysql\update_hierarchy($old, $new);
            } else {
                die("$subPackage unimplemented!");
            }
        }
    }
} else {

    if (is_dir($folder . $new)) {
        $newPyPath = $folder . $new . "/__init__.py";
        $newPy = new Text($newPyPath);
        if ($newPy->search('^@apply\b')) {
            die($newPyPath . " already exists");
        }

        $oldPyPath = $folder . $old . ".py";
        $oldPy = new Text($oldPyPath);

        $newPy->insert(0, $oldPy->readlines());

        unlink($oldPyPath);
        delete_from_init($package, $old);
    } else {

        if (file_exists($folder . $old . ".py")) {
            if (! rename($folder . $old . ".py", $folder . $new . ".py")) {
                die("failed in renaming: $folder.$old.py => $folder.$new.py");
            }
            replace_into_init($package, $old, $new);
        } else {
            $oldPath = $folder . $old . "/__init__.py";
            
            assert(file_exists($oldPath));            
            $oldText = new Text($oldPath);
            $lines = $oldText->retain('from \. import \w+');
            $newText = new Text($folder . $new . ".py");
            $newText->writelines($lines);
            
            insert_into_init($package, $new);
        }        
    }

    \mysql\update_suggest($package, $old, $new);
    $old = "$package.$old";

    if ($new == null) {
        $new = $package;
    } else
        $new = "$package.$new";

    \mysql\update_axiom($old, $new);
    \mysql\update_hierarchy($old, $new);
}

echo \std\jsonify("renamed!");
?>