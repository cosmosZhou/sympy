<?php
require_once 'utility.php';
require_once 'mysql.php';
use std\Graph, std\Text, std\Set;

function detect($theorem)
{
    // error_log(\std\jsonify($theorem));
    $G = establish_dialetic_graph($theorem);
    $graph = new Graph();
    foreach ($G as $key => $value) {
        foreach ($value as $node) {
            $graph->insert($key, $node);
        }
    }

    if (array_key_exists($theorem, $G)) {
        foreach ($G[$theorem] as $prerequisite) {
            if ($graph->detect_cycle($prerequisite)) {
                return \std\jsonify($prerequisite);
            }
        }
    }

    return null;
}

function save($codeObject)
{
    error_log("codeObject = " . \std\jsonify($codeObject));

    $module = $codeObject['module'];

    $apply = $codeObject['apply'];

    $prove = $codeObject['prove'];
    // $prove = '';
    // foreach ($codeObject['prove'] as $line) {
    // $prove .= " $line\n";
    // }

    $code = <<<EOT
    from util import *
    
    ${apply}
    
    @prove
    def prove(Eq):
    ${prove}
    
    if __name__ == '__main__':
        run()
    EOT;

    $py = module_to_py($module);

    $py = new \std\Text($py);
    $py->write($code);
    return \std\jsonify("saved");
}

$dict = empty($_POST) ? $_GET : $_POST;

foreach ($dict as $key => $args) {
    switch ($key) {
        case 'detect':
            echo detect($args);
            break;
        case 'apply':
            echo \std\jsonify(fetch_codes($args));
            break;
        case 'save':
            echo save($args);
            break;
    }
}

?>