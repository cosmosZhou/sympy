<!DOCTYPE html>
<meta charset="UTF-8">
<?php
require_once 'utility.php';

if (array_key_exists('module', $_GET)) {
    $module = $_GET['module'];
} else {
    $module = "";
}

$size = $module ? strlen($module) : 32;

list ($apply, $prove) = fetch_codes($module, true);

error_log("apply = " . \std\jsonify($apply));
error_log("prove = " . \std\jsonify($prove));

?>

<title>new theorem</title>
<link rel=stylesheet
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.css" />
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/theme/eclipse.css">
<link rel="stylesheet"
	href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.css">

<link rel="stylesheet" href="/sympy/css/codemirror.css">
<link rel="stylesheet" href="/sympy/css/style.css">


module :
<input name=module value='<?php echo $module?>' size=<?php echo $size?>
	onkeydown='onkeydown_input(this, event, false)'
	placeholder="algebra.eq.imply.eq" />
<br>

<form name=form enctype="multipart/form-data" method="post" action="">
	<textarea id='apply' name="apply"><?php echo $apply?></textarea>
	<br>
	<textarea id='prove' name="prove"><?php echo $prove?></textarea>
</form>


<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/mode/python/python.js"></script>

<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.js"></script>

<script
	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/edit/matchbrackets.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.5.1/dist/jquery.min.js"></script>
<script src="/sympy/js/std.js"></script>	
<script src="/sympy/js/utility.js"></script>
<script src="/sympy/js/new.js"></script>