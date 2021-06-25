<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<title>search</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'keyword::',
        'regularExpression::',
        'caseSensitive::',
        'wholeWord::',
    ]);
}

if (! array_key_exists("keyword", $dict)) {
    $dict["keyword"] = ".*";
    $dict["regularExpression"] = true;
}

$keyword = $dict["keyword"];
$wholeWord = array_key_exists("wholeWord", $dict) ? true : false;
$caseSensitive = array_key_exists("caseSensitive", $dict) ? true : false;
$regularExpression = array_key_exists("regularExpression", $dict) ? true : false;

error_log("keyword = $keyword");
error_log("wholeWord = $wholeWord");
error_log("caseSensitive = $caseSensitive");
error_log("regularExpression = $regularExpression");

$like = false;

$regex = $keyword;
if ($wholeWord) {
    $regex = "\\\\b$regex\\\\b";
} else if (! $regularExpression) {
    $like = true;
}

if ($like)
    $modules = \mysql\select_axiom_by_like($regex, $caseSensitive);
else
    $modules = \mysql\select_axiom_by_regex($regex, $caseSensitive);

// echo jsonify($modules);

global $user;
?>

<div id=root>
	<search-result :keyword=keyword :user=user :modules=modules
		:regular-expression=regularExpression :whole-word=wholeWord :case-sensitive=caseSensitive> 
	</search-result>
</div>

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script src="/sympy/js/std.js"></script>
<script src="/sympy/js/utility.js"></script>
<script>

	Vue.use(httpVueLoader);
	Vue.component('search-result', 'url:/sympy/vue/search-result.vue');

	var data = {
		modules : <?php echo \std\jsonify($modules)?>,
		user: <?php echo \std\jsonify($user)?>,
				
		keyword: <?php echo \std\jsonify($keyword)?>,
		regularExpression: <?php echo \std\jsonify($regularExpression)?>,
		wholeWord: <?php echo \std\jsonify($wholeWord)?>,
		caseSensitive: <?php echo \std\jsonify($caseSensitive)?>,
	};

	var app = new Vue({
		el : '#root',
		data : data, 
	});

	promise(()=>{
		$("input[type=text]")[0].focus();
	});
	
</script>