<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="/sympy/css/style.css">
<?php
require_once 'searchBox.php';
require_once 'utility.php';
require_once 'mysql.php';

$dict = $_POST;
if (array_key_exists("keyword", $_POST)) {
    $dict = $_POST;
} else {
    $dict = $_GET;
    if (! array_key_exists("keyword", $dict)) {
        $dict["keyword"] = ".*";
        $dict["regularExpression"] = true;
    }
}

$keyword = $dict["keyword"];
$wholeWord = array_key_exists("wholeWord", $dict) ? true : false;
$caseSensitive = array_key_exists("caseSensitive", $dict) ? true : false;
$regularExpression = array_key_exists("regularExpression", $dict) ? true : false;

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

?>
<title>search</title>
search results:

<div id=root>
in all, there are <?php echo count($modules)?> hits:
<br>
	<li v-for="module of modules" />
        <a :href="'/sympy/axiom.php/' + module.replace(/\./g, '/')">
        	{{module}}
        </a>
	</li>
</div>

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="utility.js"></script>
<script>	 
	search.keyword.value = <?php echo \std\jsonify($keyword)?>;
	search.regularExpression.checked = <?php echo \std\jsonify($regularExpression)?>;
	search.wholeWord.checked = <?php echo \std\jsonify($wholeWord)?>;	
	search.caseSensitive.checked = <?php echo \std\jsonify($caseSensitive)?>;	

	var data = {
		modules : <?php echo \std\jsonify($modules)?>
	};

	var app = new Vue({
		el : '#root',
		data : data, 
	});
	
	$("input[type=text]")[0].focus();
</script>