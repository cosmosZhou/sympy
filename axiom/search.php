<?php
include_once 'index.html';
require_once 'utility.php';

$keyword = $_POST["keyword"];
echo "keyword = $keyword<br>";

$wholeWord = array_key_exists("wholeWord", $_POST) ? true : false;
echo "wholeWord = $wholeWord<br>";

$caseSensitive = array_key_exists("caseSensitive", $_POST) ? true : false;
echo "caseSensitive = $caseSensitive<br>";

$regularExpression = array_key_exists("regularExpression", $_POST) ? true : false;
echo "regularExpression = $regularExpression<br>";




?>
