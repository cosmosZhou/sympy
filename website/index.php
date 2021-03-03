<?php
if (array_key_exists('lang', $_GET)) {
    $lang = $_GET['lang'];
} else {
    $lang = 'cn';
}

if (array_key_exists('section', $_GET)) {
    $section = $_GET['section'];
} else {
    $section = "home";
}

switch ($lang) {
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

        $foreignLanguage = 'cn';
        $foreignLanguageName = '中文';
        $foreignLanguageHint = 'Other Language';

        $history = 'Breif History';

        $userManual = 'User Manual';
        break;
    case 'cn':
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
        $foreignLanguage = 'en';
        $foreignLanguageName = 'English';
        $foreignLanguageHint = '其它语言';

        $history = '发展简史';
        $userManual = '操作手册';
    default:
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

			<div style="float: right">
				<?php echo $foreignLanguageHint ?>
				<a
					href='index.php?lang=<?php echo $foreignLanguage ?>&section=<?php echo $section ?>'
					align='left'><?php echo $foreignLanguageName ?></a>
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

			<div id='content'>
				<?php require_once "$lang/$section.php";?>			
			</div>
		</div>
	</div>

</body>
</html>