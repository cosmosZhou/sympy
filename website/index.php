<html>
<!-- Last updated by tpd on March 10, 2010 -->
<head>
<meta http-equiv="content-type" content="text/html;charset=utf-8" />
<link href="style.css" rel="stylesheet" type="text/css" />
<title>机械化定理推导</title>
</head>
<body>
	<div id='container'>

		<div id='header' align='center'>
			<a href="https://github.com/cosmosZhou/sympy" title='github address'><font
				size=5 color=blue>axiom.top</font></a> <br> <font size=200%> Axiomatized Mathematical Analysis System </font>
		</div>

		<hr />

		<div id='content_container'>

			<div id='sidebar'>
				<div class='sidebar_heading'>
					<a href='index.php'>Home</a>
				</div>
				<br>
				<div class='sidebar_body'>
					<a href='index.php?section=download'>Download</a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?section=help'>Help</a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?section=bugReport'>Bug Report</a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?section=participation'>Participation</a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?section=contact'>Contact Us</a>
				</div>
				<div class='sidebar_body'>
					<a href='index.php?section=roadMap'>Road Map</a>
				</div>
				<br>
				<div class='sidebar_heading'>User Guide</div>
				<div class='sidebar_body'>
					<a href="index.php?section=elementary" title="Elementary Examples">
						Elementary Examples</a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?section=intermediate"
						title="Intermediate Examples"> Intermediate Examples</a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?section=advanced" title="Advanced Examples">
						Advanced Examples</a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?section=faq" title="FAQ"> Frequently Asked
						Questions</a>
				</div>
				<div class='sidebar_body'>
					<a href="index.php?section=documentation" title="Documentation">
						Documentation</a>
				</div>
			</div>

			<div id='content'>

<?php
if (array_key_exists('section', $_GET)) {
    $section = $_GET['section'];
    require_once "$section.php";
} else {
    require_once 'home.php';
}
?>			
			</div>
		</div>
	</div>

</body>
</html>
