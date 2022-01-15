<?php
use std\Graph;

function package_is_theorem($file)
{
    global $path_info;
    $__init__ = $path_info . $file . "/__init__.py";
    // \std\println("__init__ = $__init__");
    if (file_exists($__init__)) {
        $text = new \std\Text($__init__);
        foreach ($text as $line) {
            return ! preg_match("/from *\. *import \w+/", $line, $m);
        }
    }

    return false;
}

// error_log("path_info = $path_info");
if (! \std\endsWith($path_info, '/')) {
    $path_info .= "/";
}

$theorems = [];

$packages = [];

foreach (scandir($path_info) as $file) {
    switch ($file) {
        case ".":
        case "..":
        case "__pycache__":
            break;
        case "__init__.py":
            break;
        default:
//             error_log("file = $file");

            if (\std\endsWith($file, '.py')) {
                $theorems[] = substr($file, 0, - 3);
            } else {
                if (package_is_theorem($file)) {
                    $theorems[] = $file;
                }

                $packages[] = $file;
            }
    }
}

if (\std\endsWith($title, '/')) {
    $title = substr($title, 0, - 1);
}
?>

<title><?php echo $title;?></title>
<body></body>

<script src="static/unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>

<script>
createApp('axiomContents', {
	packages: <?php echo \std\jsonify($packages)?>,
	theorems: <?php echo \std\jsonify($theorems)?>,
});
</script>



