<?php
if (array_key_exists('lang', $_GET)) {
    $lang = $_GET['lang'];
} else {
    $HTTP_ACCEPT_LANGUAGE = $_SERVER['HTTP_ACCEPT_LANGUAGE'];
    error_log("HTTP_ACCEPT_LANGUAGE = $HTTP_ACCEPT_LANGUAGE");

    if (isset($HTTP_ACCEPT_LANGUAGE) && strlen($HTTP_ACCEPT_LANGUAGE) > 1) {
        $x = explode(",", $HTTP_ACCEPT_LANGUAGE);
        foreach ($x as $val) {
            if (preg_match("/(.*);q=([0-1]{0,1}.\d{0,4})/i", $val, $matches))
                $langue[$matches[1]] = (float) $matches[2];
            else
                $langue[$val] = 1.0;
        }
        $qval = 0.0;
        foreach ($langue as $key => $value) {
            if ($value > $qval) {
                $qval = (float) $value;
                $lang = $key;
            }
        }
        if (strpos("-", $lang) >= 0){
            $lang = explode("-", $lang)[0];
        }
        //error_log("langue = ".json_encode($langue));
        //error_log("lang = ".$lang);        
    }
    else{
        $lang = 'zh';
    }
}

if (array_key_exists('section', $_GET)) {
    $section = $_GET['section'];
} else {
    $section = "home";
}

switch ($lang) {
    case 'fr':
        $title = "Système d'analyse mathématique axiomatisé";
        $home = "page d'accueil";
        $faq = 'Foire aux questions';
        $bugReport = 'Rapport de bogue';
        
        $userGuide = 'Guide de l’utilisateur';
        $participation = 'Participation';
        $contact = 'Contactez-nous';
        $roadMap = 'Carte routière';
        $elementaryExamples = 'Exemples élémentaires';
        $intermediateExamples = 'Exemples intermédiaires';
        $advancedExamples = 'Exemples avancés';
        $designManual = 'Manuel de conception';
        
        $languageSelect = 'sélectionner d’autres langues';
        
        $history = 'Histoire de Breif';
        
        $userManual = 'Manuel';
        $signIn = 'Connexion';
        $signUp = "S'enregistrer";
        break;

    case 'zh':
        $title = '机械化定理库';
        $home = '网站主页';
        $faq = '常见问题';
        $bugReport = '故障报告';

        $userGuide = '用户指南';
        $participation = '项目参与';
        $contact = '联系作者';
        $roadMap = '奋斗目标';
        $elementaryExamples = '初级例题';
        $intermediateExamples = '中级例题';
        $advancedExamples = '高级例题';
        $designManual = '设计文档';
        $languageSelect = '选择语言';

        $history = '探索历程';
        $userManual = '操作手册';
        $signIn = '登陆';
        $signUp = '注册';
        break;
    default:
    case 'en':
        
        $title = 'Axiomatized Mathematics Analysis System';
        $home = 'Home';
        $faq = 'Frequently Asked Questions';
        $bugReport = 'Bug Report';
        
        $userGuide = 'User Guide';
        $participation = 'Participation';
        $contact = 'Contact Us';
        $roadMap = 'Road Map';
        $elementaryExamples = 'Elementary Examples';
        $intermediateExamples = 'Intermediate Examples';
        $advancedExamples = 'Advanced Examples';
        $designManual = 'Design Manual';
        
        $languageSelect = 'Select Language';
        
        $history = 'Breif History';
        
        $userManual = 'User Manual';
        $signIn = 'Sign In';
        $signUp = 'Sign UP';        
        break;
}
?>

<html>
<head>
<meta http-equiv="content-type" content="text/html;charset=utf-8" />
<link href="style.css" rel="stylesheet" type="text/css" />
<title><?php echo $title ?></title>
</head>
<body>
	<div id='container'>

		<div id='header' align='center'>
			<font size=200%> <?php echo $title ?></font>

			<div style="float:right">
				<?php echo $languageSelect ?>
				<select align='left' onchange="onchange_select(this)">
					<option value=en <?php echo $lang == 'en'? 'selected': ''?>>English</option>
					<option value=zh <?php echo $lang == 'zh'? 'selected': ''?>>简体中文</option>
					<option value=fr <?php echo $lang == 'fr'? 'selected': ''?>>Français</option>
				</select>
				<br>
				<a href='signin.php?lang=<?php echo $lang ?>' align='left'><?php echo $signIn ?></a>
				<a href='signup.php?lang=<?php echo $lang ?>' align='left'><?php echo $signUp ?></a>
			</div>

		</div>

		<hr />

		<div id='content_container'>

			<div id='sidebar'>
				<div class='sidebar_heading'>
					<a href='index.php?lang=<?php echo $lang ?>'><?php echo $home ?></a>
				</div>
				<br>
				<div class='sidebar_body'>
					<a href='index.php?lang=<?php echo $lang ?>&section=bugReport'><?php echo $bugReport ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?lang=<?php echo $lang ?>&section=participation'><?php echo $participation ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?lang=<?php echo $lang ?>&section=contact'><?php echo $contact ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?lang=<?php echo $lang ?>&section=history'><?php echo $history ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?lang=<?php echo $lang ?>&section=roadMap'><?php echo $roadMap ?></a>
				</div>

				<br>
				<div class='sidebar_heading'><?php echo $userGuide ?></div>
				<br>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=elementary"
						title="<?php echo $elementaryExamples ?>">
						<?php echo $elementaryExamples ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=intermediate"
						title="<?php echo $intermediateExamples ?>"><?php echo $intermediateExamples ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=advanced"
						title="<?php echo $advancedExamples ?>">
						<?php echo $advancedExamples ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=faq"
						title="<?php echo $faq ?>"><?php echo $faq ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=designManual"
						title="<?php echo $designManual ?>"><?php echo $designManual ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?lang=<?php echo $lang ?>&section=userManual"
						title="<?php echo $userManual ?>"><?php echo $userManual ?></a>
				</div>
			</div>

			<div id='content'></div>
		</div>
	</div>

</body>
</html>

<script	src="https://cdn.jsdelivr.net/highlight.js/8.8.0/highlight.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/jquery/dist/jquery.min.js"></script>
<script src="/sympy/static/js/std.js"></script>
<script>

function onchange_select(self){
	location.href = `index.php?lang=${self.value}`;
}

hljs.initHighlightingOnLoad();

var url = `/sympy/website/md/<?php echo "$lang/$section.md" ?>`;
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
    	
        $("#content").html(marked.marked(text));
    }
});

</script>