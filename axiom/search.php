search results:
<?php
require_once 'searchBox.php';
include_once 'index.html';
require_once 'utility.php';

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

$modules = [];
foreach (read_all_php(dirname(__file__)) as $php) {
    // https://www.php.net/manual/en/function.substr.php
    $module = to_python_module($php);

    if (! $caseSensitive) {
        if ($wholeWord) {
            if (preg_match('/\\b' . $keyword . '\\b/i', $module, $matches)) {
                $modules[] = $module;
            }
        } else if ($regularExpression) {
            if (preg_match('/' . $keyword . '/i', $module, $matches)) {
                $modules[] = $module;
            }
        } else {
            if (strpos(strtolower($module), strtolower($keyword)) !== false) {
                $modules[] = $module;
            }
        }
    } else if ($wholeWord) {
        if (preg_match('/\\b' . $keyword . '\\b/', $module, $matches)) {
            $modules[] = $module;
        }
    } else if ($regularExpression) {
        if (preg_match('/' . $keyword . '/', $module, $matches)) {
            $modules[] = $module;
        }
    } else {
        if (strpos($module, $keyword) !== false) {
            $modules[] = $module;
        }
    }
}
?>

<div id=root>
in all, there are <?php echo count($modules)?> hits:
<br>
	<module :module=module v-for="module of modules" />
</div>

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="utility.js"></script>
<script>	 
	search.keyword.value = <?php echo jsonify($keyword)?>;
	search.regularExpression.checked = <?php echo jsonify($regularExpression)?>;
	search.wholeWord.checked = <?php echo jsonify($wholeWord)?>;	
	search.caseSensitive.checked = <?php echo jsonify($caseSensitive)?>;	

	var data = {
		modules : <?php echo jsonify($modules)?>
	};

	var module = {
        name: 'module',
        props: ['module'],        
        template:
        	`<li>
	            <a :href="'/sympy/' + module.replaceAll('.', '/') + '.php'">
	            	{{module}}
	            </a>                    	
            </li>`,
    };

	var components = {
		module : module,
	};
	
	var app = new Vue({
		el : '#root',
		data : data, 
		components : components
	});
	
	$("input[type=text]")[0].focus();
</script>