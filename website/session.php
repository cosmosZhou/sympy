<?php
// foreach ($_POST as $key => $value){
//     echo "$key => $value<br>";
// }

require_once '../php/mysql.php';
//require_once '../php/std.php';

$user = $_POST['login'];
$password = $_POST['password'];

$sql = "select * from tbl_login_py where user = '$user'";
foreach (\mysql\select("select password from tbl_login_py where user = '$user'") as list($password_mysql)){
    if ($password == $password_mysql){
        break;
    }
    else{
        echo $sql."<br>";
        die("password incorrect, please try again!");
    }
}

?>
<script>
	var user = `<?php echo $user?>`;
	var href = location.href;
	href = href.match(/(.+)\/sympy\/website\/session\b/)[1]; 
	href = `${href}/${user}/axiom.php`;
	location.href = href;
</script>