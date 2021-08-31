<?php
require_once '../mysql.php';

function select_timestamp($state = null)
{
    global $user;
    
    $sql = "select axiom, timestamp from tbl_axiom_py where user = '$user'";
    
    foreach (\mysql\select($sql) as $tuple) {
        yield $tuple;
    }
}

echo \std\jsonify(iterator_to_array(select_timestamp()));

?>