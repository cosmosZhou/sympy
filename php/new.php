<!DOCTYPE html>
<meta charset="UTF-8">
<?php
require_once 'utility.php';

$module = $_GET['new'];

$size = $module ? strlen($module) : 32;

$module = str_replace("/", ".", $module);

list ($apply, $prove) = fetch_codes($module, true);

error_log("apply = " . \std\jsonify($apply));
error_log("prove = " . \std\jsonify($prove));

?>

<title><?php echo $module;?></title>
<link rel=stylesheet href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.css" />
<link rel=stylesheet href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/theme/eclipse.css">
<link rel=stylesheet href="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.css">
<link rel=stylesheet href="static/css/codemirror.css">
<link rel=stylesheet href="static/css/style.css">

<script	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/lib/codemirror.js"></script>
<script	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/mode/python/python.js"></script>
<script	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/hint/show-hint.js"></script>
<script	src="https://cdn.jsdelivr.net/npm/codemirror@5.41.0/addon/edit/matchbrackets.js"></script>
	
<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src="https://unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>

<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>

<script type=module>
createApp('newTheorem', {
    apply : <?php echo \std\jsonify($apply)?>,
    prove : <?php echo \std\jsonify($prove)?>,
    module : <?php echo \std\jsonify($module)?>,
});

</script>