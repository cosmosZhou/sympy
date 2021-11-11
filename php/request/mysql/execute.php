<?php
require_once '../../mysql.php';

$sql = $_POST['sql'];
$rowcount = \mysql\execute($sql);

echo $rowcount;
?>