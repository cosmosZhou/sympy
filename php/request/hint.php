<?php
require_once '../utility.php';
require_once '../mysql.php';

$dict = empty($_POST) ? $_GET : $_POST;
$prefix = $dict['prefix'];
echo \std\jsonify(\mysql\hint($prefix));

?>