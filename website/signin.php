<?php
if (array_key_exists('lang', $_GET)) {
    $lang = $_GET['lang'];
} else {
    $lang = 'cn';
}

switch($lang){
    case 'cn':
        $header = '登陆定理库';
        $title = "$header · 定理库";
        $username = '用户名或者电子邮箱';
        $password = '登陆密码';
        $forgotPassword = '忘记密码？';
        $signIn = "登陆";
        $newCommer = "定理库新手？ ";
        $createAccount = "注册新用户";
        $terms = "条款";
        $privacy = "隐私权";
        $security = "保密声明";
        $contactAxiom = "联系作者";
        break;
    case 'en':
        $header = 'Sign in to axiom.top';
        $title = "$header · axiom.top";
        $username = 'Username or email address';
        $password = 'Password';
        $forgotPassword = 'forgot password?';
        $signIn = "Sign in";
        $newCommer = "New to GitHub? ";
        $createAccount = "Create an account";
        $terms = "Terms";
        
        $privacy = "Privacy"; 
        $security = "Security";
        $contactAxiom = "Contact axiom.top";
        
        break;
}
?>

<html lang="en" data-color-mode="auto" data-light-theme="light"
	data-dark-theme="dark">
<head>
<meta charset="utf-8">
<link rel="dns-prefetch" href="https://github.githubassets.com">
<link rel="dns-prefetch" href="https://avatars.githubusercontent.com">
<link rel="dns-prefetch" href="https://github-cloud.s3.amazonaws.com">
<link rel="dns-prefetch"
	href="https://user-images.githubusercontent.com/">



<link crossorigin="anonymous" media="all"
	integrity="sha512-B/jj6qcXmAwGUh/FG7mfpfFSb0lW1UpGiufFhzIeC+u3lXE5VDEJQzVxZ3gquw8xjZBNQ6CgWDSgCgjRzqPUgw=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/frameworks-07f8e3eaa717980c06521fc51bb99fa5.css">

<link crossorigin="anonymous" media="all"
	integrity="sha512-ncgXO/E1QqBCX+dJ6vkIJYBTGiiUacQ1lvX/XK0B2ZecI6+KfFVHuJaIJzeVJqRi9oRnsraN4UmtHWazdxx+ug=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/behaviors-9dc8173bf13542a0425fe749eaf90825.css">



<link crossorigin="anonymous" media="all"
	integrity="sha512-pigFwKshMT8s+7cYx99oWXt2K8MZ6HE5h7RGvsi0cEDlCGJU0lwASrQI1YTCAZY/8uvrg1Rx4+cyfym+/t+clQ=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/github-a62805c0ab21313f2cfbb718c7df6859.css">

<script crossorigin="anonymous" defer="defer"
	integrity="sha512-CzeY4A6TiG4fGZSWZU8FxmzFFmcQFoPpArF0hkH0/J/S7UL4eed/LKEXMQXfTwiG5yEJBI+9BdKG8KQJNbhcIQ=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/environment-0b3798e0.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-DqYNCH7iUbISz3MHrZQblQWzFkyoyanHdbyINagP5PJaZUBI/ty/b5I50KRwLWqMSur/fpUltEz4XZeRHcr1Yw=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/chunk-frameworks-0ea60d08.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-YufdcMb4hh5uM2JSDx/MEATxourBQILRY0+74aM14JruGbjAyRYNY7hr/9+MOvY/ItDDo5pyqG/MHZr+5zZKHg=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/chunk-vendor-62e7dd70.js"></script>

<script crossorigin="anonymous" defer="defer"
	integrity="sha512-xvjJoISxU0GxRhz8IzuGNcKLW8ocimwz31kpata7/nJWD/QnUQfQk8rLWd+9pC0ApRmr+7xV/MfqEyMVhXRgVA=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/behaviors-c6f8c9a0.js"></script>

<script crossorigin="anonymous" defer="defer"
	integrity="sha512-5tWKSr7mhAzSh4Sx5YRFgKftdGxKwHKnOGYw5DlxjHhkQVURYFU3Bk5IMOGMKuAiJTlC3OXYM3xzGcyjzuEFQQ=="
	type="application/javascript"
	data-module-id="./chunk-animate-on-scroll.js"
	data-src="https://github.githubassets.com/assets/chunk-animate-on-scroll-e6d58a4a.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-ct3QiK2mvpg7zor9R2psdWnNMM2K32RU4RGRB/7yA5FyZ8H4iY6SNynXc7UaJqzBx6NaReg3GsWJPwW3kgAAig=="
	type="application/javascript" data-module-id="./chunk-codemirror.js"
	data-src="https://github.githubassets.com/assets/chunk-codemirror-72ddd088.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-M6W/sGLOuJXCIkw+doDl6zl7J9q2DmqdwftQCtyEiZM/UJNGRVQdyKwI/PAMxD12se/wCx3ZcyJs9nz0o0OSVw=="
	type="application/javascript" data-module-id="./chunk-color-modes.js"
	src="https://github.githubassets.com/assets/chunk-color-modes-33a5bfb0.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-71HZu1T5JWqRNF9wrm2NXZAqYVvzxZ8Dvor5U5l/LuEBbGCBX57Sny60Rj+qUZZAvEBGFlNsz179DEn2HFwgVA=="
	type="application/javascript" data-module-id="./chunk-confetti.js"
	data-src="https://github.githubassets.com/assets/chunk-confetti-ef51d9bb.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-zkYZSjUFqSifB+Lt76jclFMrfqpcPqevT801RZcoBNCZHRTBKcFrW9OyJoPOzKFv+fZVDRnqdqGsuIv5KOIgZg=="
	type="application/javascript"
	data-module-id="./chunk-contributions-spider-graph.js"
	data-src="https://github.githubassets.com/assets/chunk-contributions-spider-graph-ce46194a.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-6j/oSF+kbW+yetNPvI684VzAu9pzug6Vj2h+3u1LdCuRhR4jnuiHZfeQKls3nxcT/S3H+oIt7FtigE/aeoj+gg=="
	type="application/javascript" data-module-id="./chunk-drag-drop.js"
	data-src="https://github.githubassets.com/assets/chunk-drag-drop-ea3fe848.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-VSSd+Yzi2iMS+pibY6hD/WdypxAEdob5F2RMKxuKcAHS2EpFYJPeTXoVxt0NXg03tfj2dka2mEtHS+vjpYSaDw=="
	type="application/javascript"
	data-module-id="./chunk-edit-hook-secret-element.js"
	data-src="https://github.githubassets.com/assets/chunk-edit-hook-secret-element-55249df9.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-N+ziqJjVMfWiqeVHdayDHpNRlG5HsF+cgV+pFnMDoTJuvBzgw+ndsepe4NcKAxIS3WMvzMaQcYmd2vrIaoAJVg=="
	type="application/javascript" data-module-id="./chunk-edit.js"
	src="https://github.githubassets.com/assets/chunk-edit-37ece2a8.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-aiqMIGGZGo8AQMjcoImKPMTsZVVRl6htCSY7BpRmpGPG/AF+Wq+P/Oj/dthWQOIk9cCNMPEas7O2zAR6oqn0tA=="
	type="application/javascript"
	data-module-id="./chunk-emoji-picker-element.js"
	data-src="https://github.githubassets.com/assets/chunk-emoji-picker-element-6a2a8c20.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-rLdDFAJkSow9YL/I6cWs9Nx790rbDALMvJZ90DQfolTEzxyzh7vEYdM2CrWeCoAaC+aoMQI2btzMFlZ43l5cGA=="
	type="application/javascript" data-module-id="./chunk-filter-input.js"
	data-src="https://github.githubassets.com/assets/chunk-filter-input-acb74314.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-Z1wcyOFQHzyMSPqp5DLKrobr3DN2Q6Dz31cfPtw4b2vPs9PX0PrxyDXHpTbIlcZ9qT1M1BNAypHKKw8Lp6Yx/Q=="
	type="application/javascript"
	data-module-id="./chunk-insights-graph.js"
	data-src="https://github.githubassets.com/assets/chunk-insights-graph-675c1cc8.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-4iRI95LO0kKcZLWUoOzqI6w8IVGppDVluR4dL7yyz8zgBu/7JAib0MkRN5LUVxXv0KIT6mQ2m5jbKa1NeZoD5A=="
	type="application/javascript" data-module-id="./chunk-invitations.js"
	src="https://github.githubassets.com/assets/chunk-invitations-e22448f7.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-Dhn0P9aANkDPzMxpqETLGel8ELkO93wrLFrMnEOSg8DguOxR7UNY1MyL3lexSVWo/ZZvme3kcWTaM6gw/DJW1w=="
	type="application/javascript" data-module-id="./chunk-jump-to.js"
	data-src="https://github.githubassets.com/assets/chunk-jump-to-0e19f43f.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-0DSZHh/iD27pAOXl4AWcxPqgRsJAVr1M8SnaN4gKYH2ZplPywvL5oalqN4Qj03FsB5Ll0pytD5kiTMibgGq0BA=="
	type="application/javascript"
	data-module-id="./chunk-launch-code-element.js"
	data-src="https://github.githubassets.com/assets/chunk-launch-code-element-d034991e.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-RduaLAviB2ygvRK/eX5iwzYO43ie7svrJ0rYJs06x7XqpRl/IK8PPBscBWM9Moo5Z86DK2iRLE2+aR7TJ5Uc2Q=="
	type="application/javascript"
	data-module-id="./chunk-metric-selection-element.js"
	data-src="https://github.githubassets.com/assets/chunk-metric-selection-element-45db9a2c.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-Lo0j1owPfYM0txt85KwGzF1PQJLvLFGbRJoASd5ZKMQAV9ZSDg5bVm5UWBAz7glGzw1pkiUD2bCMs2wqyf+CEA=="
	type="application/javascript"
	data-module-id="./chunk-notification-list-focus.js"
	src="https://github.githubassets.com/assets/chunk-notification-list-focus-2e8d23d6.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-ma0OOy3nj0c1cqBx0BkcmIFsLqcSZ+MIukQxyEFM/OWTzZpG+QMgOoWPAHZz43M6fyjAUG1jH6c/6LPiiKPCyw=="
	type="application/javascript"
	data-module-id="./chunk-profile-pins-element.js"
	data-src="https://github.githubassets.com/assets/chunk-profile-pins-element-99ad0e3b.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-/kPLzWIe41nxla5A+wcKKPIw4xiAsuITdjbXGVCycmUYnADfCids8FdV+TCA68gr4jAhKIws7flLpL12MoouBA=="
	type="application/javascript"
	data-module-id="./chunk-readme-toc-element.js"
	data-src="https://github.githubassets.com/assets/chunk-readme-toc-element-fe43cbcd.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-nesU0auizp1y0FhtbdzngFVjBVsBEIk/VIVbhC+LcHpGJltFDE7hGwjT8EAbOK5YXTC2cNmheObIukXFtQBtZw=="
	type="application/javascript" data-module-id="./chunk-ref-selector.js"
	data-src="https://github.githubassets.com/assets/chunk-ref-selector-9deb14d1.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-Pdw73fp9TN1At4AjDI1042MNWNj/i0OczklFSWkHaUt+d9P1ZlXV/Msu3rHncrs6xRca2WznxDWlgYRsPRyP1w=="
	type="application/javascript"
	data-module-id="./chunk-responsive-underlinenav.js"
	src="https://github.githubassets.com/assets/chunk-responsive-underlinenav-3ddc3bdd.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-UUeOf6fdSNCh5PEil2eqo9JMci+9FbJ2YdzZ1rE8fFMYtanaPRRJSidxpPbnl16jxAuQo0QzosPRMKbiFuN0sQ=="
	type="application/javascript" data-module-id="./chunk-runner-groups.js"
	src="https://github.githubassets.com/assets/chunk-runner-groups-51478e7f.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-tk76eoSLUqXSVZ8ANzPprrOImFIV1zQ/VBV+WzG8ZjZpVPH8cLkMH/ur5HJB1lxx9/yo+V2wjDF96t4qfUwZLA=="
	type="application/javascript"
	data-module-id="./chunk-severity-calculator-element.js"
	data-src="https://github.githubassets.com/assets/chunk-severity-calculator-element-b64efa7a.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-fIq9Mn7jY/bHQXnsmh+VejpDnaO+d/FDxsp+4CuZtdNLrLuO+dQCjh+m6Yd8GCYD2Cy6DWbCEyM+mH2dkB2H9A=="
	type="application/javascript"
	data-module-id="./chunk-sortable-behavior.js"
	data-src="https://github.githubassets.com/assets/chunk-sortable-behavior-7c8abd32.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-WK8VXw3lfUQ/VRW0zlgKPhcMUqH0uTnB/KzePUPdZhCm/HpxfXXHKTGvj5C0Oex7+zbIM2ECzULbtTCT4ug3yg=="
	type="application/javascript" data-module-id="./chunk-toast.js"
	data-src="https://github.githubassets.com/assets/chunk-toast-58af155f.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-vgHJEmEJxNmHucGbVY8bEUoOYo5/ZwpQ69rU8Dld89daWJ54uad9lNptxq32F8pnbHhdngw9lohNEbMbjmj5AQ=="
	type="application/javascript" data-module-id="./chunk-tweetsodium.js"
	data-src="https://github.githubassets.com/assets/chunk-tweetsodium-be01c912.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-SLqYSMMqthFrVCoXJeZhRyCtWXUsJCUHhj+FJ+bQaBxPTNh+1X0WxCX8u1KQF9eGovmnZUGLEFbUI8PpXhUTXQ=="
	type="application/javascript"
	data-module-id="./chunk-user-status-submit.js"
	data-src="https://github.githubassets.com/assets/chunk-user-status-submit-48ba9848.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-nub3hcrozKxxha7BygBmzSmVQYk5JFRCnsxrem3CHN2TeFs2FI+gXC1TqIAaovdKQUpqWm63G3Oh4ToKuZi17A=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/unsupported-9ee6f785.js"></script>

<script crossorigin="anonymous" defer="defer"
	integrity="sha512-meGxncMhxgALvcLa91y5ghCSrSFmp0U4sIbJpJdBuIRGodRjfG5RGmV34i4oWIp3eIVMJ1Npm1OYMk7JIaCDiQ=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/settings-99e1b19d.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-F/YgidVyCM3/yTpiyJSKMrsyVvATFAT4GdPDVWL81w3jTVKHRryYBq1jwQFfiUlYm8/nJ47y2r74sDxQBaCLiw=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/sessions-17f62089.js"></script>

<meta name="viewport" content="width=device-width">

<title><?php echo $title?></title>
<meta name="description"
	content="GitHub is where people build software. More than 65 million people use GitHub to discover, fork, and contribute to over 200 million projects.">
<link rel="search" type="application/opensearchdescription+xml"
	href="/opensearch.xml" title="GitHub">
<link rel="fluid-icon" href="https://github.com/fluidicon.png"
	title="GitHub">
<meta property="fb:app_id" content="1401488693436528">

<meta property="og:url" content="https://github.com">
<meta property="og:site_name" content="GitHub">
<meta property="og:title" content="Build software better, together">
<meta property="og:description"
	content="GitHub is where people build software. More than 65 million people use GitHub to discover, fork, and contribute to over 200 million projects.">
<meta property="og:image"
	content="https://github.githubassets.com/images/modules/open_graph/github-logo.png">
<meta property="og:image:type" content="image/png">
<meta property="og:image:width" content="1200">
<meta property="og:image:height" content="1200">
<meta property="og:image"
	content="https://github.githubassets.com/images/modules/open_graph/github-mark.png">
<meta property="og:image:type" content="image/png">
<meta property="og:image:width" content="1200">
<meta property="og:image:height" content="620">
<meta property="og:image"
	content="https://github.githubassets.com/images/modules/open_graph/github-octocat.png">
<meta property="og:image:type" content="image/png">
<meta property="og:image:width" content="1200">
<meta property="og:image:height" content="620">

<meta property="twitter:site" content="github">
<meta property="twitter:site:id" content="13334762">
<meta property="twitter:creator" content="github">
<meta property="twitter:creator:id" content="13334762">
<meta property="twitter:card" content="summary_large_image">
<meta property="twitter:title" content="GitHub">
<meta property="twitter:description"
	content="GitHub is where people build software. More than 65 million people use GitHub to discover, fork, and contribute to over 200 million projects.">
<meta property="twitter:image:src"
	content="https://github.githubassets.com/images/modules/open_graph/github-logo.png">
<meta property="twitter:image:width" content="1200">
<meta property="twitter:image:height" content="1200">





<link rel="assets" href="https://github.githubassets.com/">


<meta name="request-id" content="E547:374A:15CECA1:16FB1D6:60CC27A9"
	data-pjax-transient="true">
<meta name="html-safe-nonce"
	content="b0258bd3cabd971b34197e0bd716d8e61b075d14fa55d95c015a140537c60253"
	data-pjax-transient="true">
<meta name="visitor-payload"
	content="eyJyZWZlcnJlciI6bnVsbCwicmVxdWVzdF9pZCI6IkU1NDc6Mzc0QToxNUNFQ0ExOjE2RkIxRDY6NjBDQzI3QTkiLCJ2aXNpdG9yX2lkIjoiNTA5OTU2MjQ0OTEwNDQ1NzgyMSIsInJlZ2lvbl9lZGdlIjoiYXAtc291dGhlYXN0LTEiLCJyZWdpb25fcmVuZGVyIjoiaWFkIn0="
	data-pjax-transient="true">
<meta name="visitor-hmac"
	content="19743a810ce270a005553191652e4361b83210695b5ad48b05f72c74b8f7d98c"
	data-pjax-transient="true">



<meta name="github-keyboard-shortcuts" content=""
	data-pjax-transient="true">



<meta name="selected-link" value="/login" data-pjax-transient="">

<meta name="google-site-verification"
	content="c1kuD-K2HIVF635lypcsWPoD4kilo5-jA_wBFyT4uMY">
<meta name="google-site-verification"
	content="KT5gs8h0wvaagLKAVWq8bbeNwnZZK1r1XQysX3xurLU">
<meta name="google-site-verification"
	content="ZzhVyEFwb7w3e0-uOTltm8Jsck2F5StVihD0exw2fsA">
<meta name="google-site-verification"
	content="GXs5KoUUkNCoaAZn7wPN-t01Pywp9M3sEjnt_3_ZWPc">

<meta name="octolytics-host" content="collector.githubapp.com">
<meta name="octolytics-app-id" content="github">
<meta name="octolytics-event-url"
	content="https://collector.githubapp.com/github-external/browser_event">

<meta name="analytics-location-query-strip" content="true"
	data-pjax-transient="true">










<meta name="hostname" content="github.com">
<meta name="user-login" content="">


<meta name="expected-hostname" content="github.com">


<meta name="enabled-features"
	content="MARKETPLACE_PENDING_INSTALLATIONS,AUTOCOMPLETE_EMOJIS_IN_MARKDOWN_EDITOR">

<meta http-equiv="x-pjax-version"
	content="f0198a441fc73b076daa939dd7112001026079775aafde2ccb5b44a397b79333">


<link crossorigin="anonymous" media="all"
	integrity="sha512-pigFwKshMT8s+7cYx99oWXt2K8MZ6HE5h7RGvsi0cEDlCGJU0lwASrQI1YTCAZY/8uvrg1Rx4+cyfym+/t+clQ=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/github-a62805c0ab21313f2cfbb718c7df6859.css">



<link rel="canonical" href="https://github.com/login"
	data-pjax-transient="">


<meta name="browser-stats-url"
	content="https://api.github.com/_private/browser/stats">

<meta name="browser-errors-url"
	content="https://api.github.com/_private/browser/errors">

<meta name="browser-optimizely-client-errors-url"
	content="https://api.github.com/_private/browser/optimizely_client/errors">

<link rel="mask-icon"
	href="https://github.githubassets.com/pinned-octocat.svg"
	color="#000000">
<link rel="alternate icon" class="js-site-favicon" type="image/png"
	href="https://github.githubassets.com/favicons/favicon.png">
<link rel="icon" class="js-site-favicon" type="image/svg+xml"
	href="https://github.githubassets.com/favicons/favicon.svg">

<meta name="theme-color" content="#1e2327">
<meta name="color-scheme" content="light dark">


<link rel="manifest" href="manifest.json" crossorigin="use-credentials">

<meta name="enabled-homepage-translation-languages" content="">

</head>

<body
	class="logged-out env-production page-responsive session-authentication"
	style="word-wrap: break-word;">


	<div class="position-relative js-header-wrapper ">
		<a href="#start-of-content"
			class="px-2 py-4 color-bg-info-inverse color-text-white show-on-focus js-skip-to-content">Skip
			to content</a> <span data-view-component="true"
			class="progress-pjax-loader width-full js-pjax-loader-bar Progress position-fixed">
			<span style="background-color: #79b8ff; width: 0%;"
			data-view-component="true"
			class="Progress-item progress-pjax-loader-bar"></span>
		</span>


		<div id="unsupported-browser" class="unsupported-browser" hidden="">
			<div
				class="container-lg p-responsive clearfix d-flex flex-items-center py-2">
				<svg height="16"
					class="octicon octicon-alert mr-2 color-gray-7 hide-sm"
					viewBox="0 0 16 16" version="1.1" width="16" aria-hidden="true">
					<path fill-rule="evenodd"
						d="M8.22 1.754a.25.25 0 00-.44 0L1.698 13.132a.25.25 0 00.22.368h12.164a.25.25 0 00.22-.368L8.22 1.754zm-1.763-.707c.659-1.234 2.427-1.234 3.086 0l6.082 11.378A1.75 1.75 0 0114.082 15H1.918a1.75 1.75 0 01-1.543-2.575L6.457 1.047zM9 11a1 1 0 11-2 0 1 1 0 012 0zm-.25-5.25a.75.75 0 00-1.5 0v2.5a.75.75 0 001.5 0v-2.5z"></path></svg>
				<div class="d-flex flex-auto flex-column flex-md-row">
					<div class="flex-auto min-width-0 mr-2" style="padding-top: 1px">
						<span>GitHub no longer supports this web browser.</span> <a
							href="https://docs.github.com/articles/supported-browsers"> Learn
							more about the browsers we support. </a>
					</div>
				</div>
			</div>
		</div>



		<div class="header header-logged-out width-full pt-5 pb-4"
			role="banner">
			<div class="container clearfix width-full text-center">
				<a class="header-logo" href="index.php?lang=<?php echo $lang?>"
					aria-label="Homepage"
					data-ga-click="(Logged out) Header, go to homepage, icon:logo-wordmark">
					<svg aria-hidden="true" viewBox="0 0 16 16" version="1.1"
						data-view-component="true" height="48" width="48"
						class="octicon octicon-mark-github">
    <path fill-rule="evenodd"
							d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"></path>
</svg>
				</a>
			</div>
		</div>


	</div>

	<div id="start-of-content" class="show-on-focus"></div>

	<include-fragment class="js-notification-shelf-include-fragment"
		data-base-src="https://github.com/notifications/beta/shelf"></include-fragment>

	<div class="application-main " data-commit-hovercards-enabled=""
		data-discussion-hovercards-enabled=""
		data-issue-and-pr-hovercards-enabled="">
		<main id="js-pjax-container" data-pjax-container="">



			<div class="auth-form px-3" id="login">


				<input type="hidden" name="ga_id" class="js-octo-ga-id-input">
				<div class="auth-form-header p-0">
					<h1><?php echo $header?></h1>
				</div>


				<div data-pjax-replace="" id="js-flash-container">
				</div>


				<div class="flash js-transform-notice" hidden="">
					<button class="flash-close js-flash-close" type="button"
						aria-label="Dismiss this message">
						<svg aria-label="Dismiss" role="img" viewBox="0 0 16 16"
							version="1.1" data-view-component="true" height="16" width="16"
							class="octicon octicon-x">
    						<path fill-rule="evenodd"
								d="M3.72 3.72a.75.75 0 011.06 0L8 6.94l3.22-3.22a.75.75 0 111.06 1.06L9.06 8l3.22 3.22a.75.75 0 11-1.06 1.06L8 9.06l-3.22 3.22a.75.75 0 01-1.06-1.06L6.94 8 3.72 4.78a.75.75 0 010-1.06z"></path>
						</svg>
					</button>
				</div>

				<div class="auth-form-body mt-3">

					<form action="session" accept-charset="UTF-8" method="post">
						<label for="login_field"> <?php echo $username?> </label> <input
							type="text" name="login" id="login_field"
							class="form-control input-block" autocapitalize="off"
							autocorrect="off" autocomplete="username" autofocus="autofocus">

						<div class="position-relative">
							<label for="password"> <?php echo $password ?></label> <input type="password"
								name="password" id="password"
								class="form-control form-control input-block"
								autocomplete="current-password"> <input type="hidden"
								name="trusted_device" id="trusted_device" class="form-control">
								
								
								
								 
								
								<input type="submit" name="commit"
								value="<?php echo $signIn?>" class="btn btn-primary btn-block"
								data-disable-with="Signing in…"> <a
								class="label-link position-absolute top-0 right-0" tabindex="0"
								href="/password_reset"><?php echo $forgotPassword?></a>
						</div>
					</form>
				</div>


				<p class="login-callout mt-3">
					<?php echo $newCommer?><a data-ga-click="Sign in, switch to sign up"
						data-hydro-click="{&quot;event_type&quot;:&quot;authentication.click&quot;,&quot;payload&quot;:{&quot;location_in_page&quot;:&quot;sign in switch to sign up&quot;,&quot;repository_id&quot;:null,&quot;auth_type&quot;:&quot;SIGN_UP&quot;,&quot;originating_url&quot;:&quot;https://github.com/login&quot;,&quot;user_id&quot;:null}}"
						data-hydro-click-hmac="72d062e79bb6ab076a3b88b32943286ea51894183bd812a5038d00013946f239"
						href="/signup?source=login"><?php echo $createAccount?></a>.
				</p>
			</div>

		</main>
	</div>

	<div class="footer container-lg p-responsive py-6 mt-6 f6"
		role="contentinfo">
		<ul class="list-style-none d-flex flex-justify-center">
			<li class="mr-3"><a href="/site/terms"
				data-ga-click="Footer, go to terms, text:terms"><?php echo $terms?></a></li>
			<li class="mr-3"><a href="/site/privacy"
				data-ga-click="Footer, go to privacy, text:privacy"><?php echo $privacy?></a></li>
			<li class="mr-3"><a
				href="https://docs.github.com/articles/github-security/"
				data-ga-click="Footer, go to security, text:security"><?php echo $security?></a></li>
			<li><a class="Link--secondary"
				data-ga-click="Footer, go to contact, text:contact"
				href="https://github.com/contact"><?php echo $contactAxiom?></a></li>
		</ul>
	</div>


	<div class="js-stale-session-flash flash flash-warn flash-banner"
		hidden="">
		<svg aria-hidden="true" viewBox="0 0 16 16" version="1.1"
			data-view-component="true" height="16" width="16"
			class="octicon octicon-alert">
    		<path fill-rule="evenodd"
				d="M8.22 1.754a.25.25 0 00-.44 0L1.698 13.132a.25.25 0 00.22.368h12.164a.25.25 0 00.22-.368L8.22 1.754zm-1.763-.707c.659-1.234 2.427-1.234 3.086 0l6.082 11.378A1.75 1.75 0 0114.082 15H1.918a1.75 1.75 0 01-1.543-2.575L6.457 1.047zM9 11a1 1 0 11-2 0 1 1 0 012 0zm-.25-5.25a.75.75 0 00-1.5 0v2.5a.75.75 0 001.5 0v-2.5z"></path>
		</svg>
		<span class="js-stale-session-flash-signed-in" hidden="">You signed in
			with another tab or window. <a href="">Reload</a> to refresh your
			session.
		</span> <span class="js-stale-session-flash-signed-out" hidden="">You
			signed out in another tab or window. <a href="">Reload</a> to refresh
			your session.
		</span>
	</div>
	
	<div class="Popover js-hovercard-content position-absolute"
		style="display: none; outline: none;" tabindex="0">
		<div
			class="Popover-message Popover-message--bottom-left Popover-message--large Box color-shadow-large"
			style="width: 360px;"></div>
	</div>

	<div aria-live="polite" class="sr-only"></div>
</body>
</html>
