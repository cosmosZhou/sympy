<?php
require_once '../../mysql.php';

global $user;
list (list ($port)) = iterator_to_array(\mysql\select("select port from tbl_login_py where user = '$user'"));

echo $port;
?>