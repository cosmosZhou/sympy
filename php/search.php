<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<title>search</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'std.php';

$dict = empty($_POST) ? $_GET : $_POST;

if (! $dict) {
    // https://www.php.net/manual/en/function.getopt.php
    $dict = getopt("", [
        'keyword::',
        'regularExpression::',
        'caseSensitive::',
        'wholeWord::'
    ]);
}

if (! array_key_exists("keyword", $dict)) {
    if (array_key_exists("state", $dict)) {
        $state = $dict["state"];
        $dict["keyword"] = null;
    } else {
        $dict["keyword"] = ".*";
        $dict["regularExpression"] = true;
    }
}

$keyword = $dict["keyword"];
$wholeWord = array_key_exists("wholeWord", $dict) ? true : false;
$caseSensitive = array_key_exists("caseSensitive", $dict) ? true : false;
$regularExpression = array_key_exists("regularExpression", $dict) ? true : false;
$nlp = array_key_exists("nlp", $dict) ? true : false;

error_log("wholeWord = $wholeWord");
error_log("caseSensitive = $caseSensitive");
error_log("regularExpression = $regularExpression");
error_log("nlp = $nlp");

$like = false;

$regex = $keyword;
if ($wholeWord) {
    $regex = "\\\\b$regex\\\\b";
} else if ($regularExpression) {
    $regex = str_replace("\\", "\\\\", $regex);
} else {
    $like = true;
}

if ($nlp){    
    $modules = [];
    foreach (\std\list_all_files(dirname(dirname(__file__)).'/axiom', 'py') as $py){
        $file = new \std\Text($py);
        //error_log("py = $py");
        if (!$regularExpression && $file->find($keyword) || $regularExpression && $file->search($keyword)){
            error_log("py = $py");
            $modules[] = py_to_module($py);
        }
    }
}
elseif ($like) {
    if ($regex == null) {
        $modules = \mysql\select_axiom_by_state($state);
    } else {
        $modules = \mysql\select_axiom_by_like($regex, $caseSensitive);
    }
} else {
    $modules = \mysql\select_axiom_by_regex($regex, $caseSensitive);
}

// error_log(\std\jsonify($modules));

global $user;
?>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src="static/unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>
<script type=module>
createApp('searchResult', {
    modules : <?php echo \std\jsonify($modules)?>,
	user: <?php echo \std\jsonify($user)?>,
	keyword: <?php echo \std\jsonify($keyword)?>,
	regularExpression: <?php echo \std\jsonify($regularExpression)?>,
	wholeWord: <?php echo \std\jsonify($wholeWord)?>,
	caseSensitive: <?php echo \std\jsonify($caseSensitive)?>,
});

</script>