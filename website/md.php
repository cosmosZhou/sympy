<?php


$PATH_INFO = $_SERVER["PATH_INFO"];

if (preg_match('/(\w+)\/.+\.md/', $PATH_INFO, $m)) {
    $lang = $m[1];
} else {
    require_once '../php/std.php';
    
    $path = dirname(__file__) . "/md$PATH_INFO";
    $prefix = std\startsWith($PATH_INFO, '/')? substr($PATH_INFO, 1): $PATH_INFO;
    
    $index = strrpos($prefix, '/');
    if ($index !== false){
        $prefix = substr($prefix, $index + 1);
    }
    
    foreach (scandir($path) as $name) {
        switch ($name) {
            case ".":
            case "..":
                break;
            default:
                $file = "$path/$name";
                if (is_dir($file)) {
                    $md = "$file.md";
                    if (!is_file($md))
                        echo "<a href=$prefix/$name>$name</a><br><br>";
                } else {
                    echo "<a href=$prefix/$name>$name</a><br><br>";
                }
        }
    }

    exit();
}

switch ($lang) {
    case 'en':
        $title = 'MarkDown Documents';
        break;
    case 'cn':
        $title = '标记文档';
    default:
        break;
}

?>

<html>

<head>
<meta http-equiv="content-type" content="text/html;charset=utf-8" />
<link rel=stylesheet
	href="https://cdn.jsdelivr.net/highlight.js/8.8.0/styles/default.min.css" />
<title><?php echo $title ?></title>
<style>
body {
	background-color: rgb(199, 237, 204);
	margin-left: 2.5em;
}
</style>
</head>

<body>
	<div id=content></div>
</body>

</html>

<script
	src="https://cdn.jsdelivr.net/highlight.js/8.8.0/highlight.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>
<script src="/sympy/static/js/std.js"></script>
<script> 
	hljs.initHighlightingOnLoad();

	var url = `/sympy/website/md<?php echo $PATH_INFO ?>`;
    $.ajax({
        url: url,
        type: "GET",
        dataType: "text", 
        success: function(text) {
        	url = url.slice(0, -3);
        	var newText = [];
        	var start = 0;
        	for (let m of text.matchAll(/(?<=\n)!\[(.+)\]\((.+)\)/g)){            	
            	var title = m[1];            	
            	var address = url + m[2].match(/[^\/]+(\/.+)/)[1];
            	var link = `![${title}](${address})`;
            	console.log(link);

            	newText.push(text.slice(start, m.index));
            	newText.push(link);
            	start = m.index + m[0].length;
            }

        	newText.push(text.slice(start));
        	text = newText.join('');
        	
            $("#content").html(marked(text));
        }
     })
    
</script>