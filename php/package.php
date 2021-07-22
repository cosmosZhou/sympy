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
// \std\println("path_info = $path_info");

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

$module = substr($PATH_INFO, 1);
if (\std\endsWith($module, '/')) {
    $module = substr($module, 0, - 1);
}

?>

<title><?php echo $module;?></title>

<div id=root>
	<axiom-contents :packages=packages :theorems=theorems></axiom-contents>
</div>

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src="https://cdn.jsdelivr.net/npm/vue-async-computed@3.3.1/dist/vue-async-computed.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue-resource@1.5.1/dist/vue-resource.min.js"></script>
<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>
<script>
	var module = '<?php echo $module?>';
	var packages = <?php echo \std\jsonify($packages)?>;	
	var theorems = <?php echo \std\jsonify($theorems)?>;

	Vue.use(httpVueLoader);
	Vue.use(AsyncComputed);

	Vue.component('axiom-contents', 'url:static/vue/axiom-contents.vue');

	var data = {
		packages: packages,
		theorems: theorems,
	};

	//console.log("data = " + JSON.stringify(data));

	var app = new Vue({
		el: '#root',
		data: data,	
	});

	promise(()=>{
		document.querySelector('.theorem, .package').focus();
	});
</script>



