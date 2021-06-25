<?php
$PATH_INFO = $_SERVER["PATH_INFO"];

if (preg_match('/(\w+)\/.+\.md/', $PATH_INFO, $m)) {
    $lang = $m[1];
} else {
    die("illegal path info: $PATH_INFO");
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
<link rel=stylesheet href="https://cdn.jsdelivr.net/highlight.js/8.8.0/styles/default.min.css" />
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

<script	src="https://cdn.jsdelivr.net/highlight.js/8.8.0/highlight.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>
<script> 
	hljs.initHighlightingOnLoad();

	var url = `/sympy/website/md<?php echo $PATH_INFO ?>`;
    $.ajax({
        url: url,
        type: "GET",
        dataType: "text", 
        success: function(data) {
            $("#content").html(marked(data));
        }
     })
    
</script>