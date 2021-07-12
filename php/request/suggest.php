<?php
require_once '../utility.php';
require_once '../mysql.php';

$dict = empty($_POST) ? $_GET : $_POST;

$prefix = $dict['prefix'];
$phrase = array_key_exists('phrase', $dict) ? $dict['phrase'] : '';

echo \std\jsonify(\mysql\suggest($prefix, $phrase));

?>