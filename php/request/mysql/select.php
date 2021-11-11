<?php
require_once '../../mysql.php';

$sql = $_POST['sql'];
$array = [];
foreach (\mysql\select($sql) as $row){
    $array[] = $row;
}
echo \std\jsonify($array);
?>