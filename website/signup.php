<?php
if (array_key_exists('lang', $_GET)) {
    $lang = $_GET['lang'];
} else {
    $lang = 'cn';
}

switch ($lang) {
    case 'cn':
        $header = '登陆定理库';
        $title = "加入 axiom.top · axiom.top";
        
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
        $typingEffect = "[&quot;欢迎加入axiom.top！&quot;, &quot;让我们开启机器证明之旅&quot;]";
        
        $enterEmail = "填写您的电子邮箱";
        $continue = "继续";
        $buttonWidth = "64px";
        
        $alreadyExists = "已经注册了用户名？";
        
        break;
    case 'en':
        $header = 'Sign in to axiom.top';
        $title = "Join axiom.top · axiom.top";
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
        $typingEffect = "[&quot;Welcome to axiom.top!&quot;, &quot;Let’s begin the adventure of Automated Theorem Proving&quot;]";
        
        $enterEmail = "Enter your email";
        $continue = "Continue";
        $buttonWidth = "auto";
        
        $alreadyExists = "Already have an account?";
        break;
}
?>

<html lang="en" class="height-full" data-color-mode="auto"
	data-light-theme="light" data-dark-theme="dark">
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
	integrity="sha512-67F10rfSfTBmlcjrFzNbEaTNE7h2zVYR2jfCgaBnLFUenRBPQnvMI6pD1717LNyS9bqYclUJXR88+OM3CU23YA=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/signup-ebb175d2b7d27d306695c8eb17335b11.css">
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
	data-src="https://github.githubassets.com/assets/chunk-invitations-e22448f7.js"></script>
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
	data-src="https://github.githubassets.com/assets/chunk-runner-groups-51478e7f.js"></script>
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
	integrity="sha512-avt6G0/OxaFiqy0xLxH+e387JNOqPoGcuX34lnJPQ3XHJJMzFedeknCZfD4oFPlIU4iId7RQ3CPevRw2vAcZuA=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/signup-redesign-6afb7a1b.js"></script>
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-i8CmCLlWqXPrpxdU8NXeMCuDbSZu+bbBhjD9CCbPwK04dbB9EujXbDUaPbYYkCbqZgr+TBL9oaIlRB5kBI9v3Q=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/signup-8bc0a608.js"></script>



<meta name="viewport" content="width=device-width">

<title><?php echo $title?></title>
<link rel="search" type="application/opensearchdescription+xml" href="/opensearch.xml" title="axiom">
<link rel="fluid-icon" href="png/fluidicon.png" title="axiom">


<link rel="assets" href="https://github.githubassets.com/">


<meta name="request-id" content="C4B4:51F8:AD19D5:BF45AF:60CC4876"
	data-pjax-transient="true">
<meta name="html-safe-nonce"
	content="171f76c6ec30fa506245ebe953048de95c70f435cb427ab88b636d1ba5c18b48"
	data-pjax-transient="true">
<meta name="visitor-payload"
	content="eyJyZWZlcnJlciI6Imh0dHBzOi8vZ2l0aHViLmNvbS8iLCJyZXF1ZXN0X2lkIjoiQzRCNDo1MUY4OkFEMTlENTpCRjQ1QUY6NjBDQzQ4NzYiLCJ2aXNpdG9yX2lkIjoiNTA5OTU2MjQ0OTEwNDQ1NzgyMSIsInJlZ2lvbl9lZGdlIjoiYXAtc291dGhlYXN0LTEiLCJyZWdpb25fcmVuZGVyIjoiYXAtc291dGhlYXN0LTEifQ=="
	data-pjax-transient="true">
<meta name="visitor-hmac"
	content="2ebdaca4605d4006082b9ae7a6848487769f7d86911933d7d43ba1fe0cb49e41"
	data-pjax-transient="true">



<meta name="github-keyboard-shortcuts" content=""
	data-pjax-transient="true">



<meta name="selected-link" value="/signup" data-pjax-transient="">

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







<meta name="optimizely-datafile"
	content="{&quot;version&quot;: &quot;4&quot;, &quot;rollouts&quot;: [], &quot;typedAudiences&quot;: [], &quot;anonymizeIP&quot;: true, &quot;projectId&quot;: &quot;16737760170&quot;, &quot;variables&quot;: [], &quot;featureFlags&quot;: [], &quot;experiments&quot;: [{&quot;status&quot;: &quot;Running&quot;, &quot;audienceIds&quot;: [], &quot;variations&quot;: [{&quot;variables&quot;: [], &quot;id&quot;: &quot;20227754799&quot;, &quot;key&quot;: &quot;control&quot;}, {&quot;variables&quot;: [], &quot;id&quot;: &quot;20233267869&quot;, &quot;key&quot;: &quot;treatment&quot;}], &quot;id&quot;: &quot;20194668672&quot;, &quot;key&quot;: &quot;recommended_plan_in_signup&quot;, &quot;layerId&quot;: &quot;20231804245&quot;, &quot;trafficAllocation&quot;: [{&quot;entityId&quot;: &quot;20233267869&quot;, &quot;endOfRange&quot;: 2500}, {&quot;entityId&quot;: &quot;&quot;, &quot;endOfRange&quot;: 5000}, {&quot;entityId&quot;: &quot;20227754799&quot;, &quot;endOfRange&quot;: 7500}, {&quot;entityId&quot;: &quot;&quot;, &quot;endOfRange&quot;: 10000}], &quot;forcedVariations&quot;: {&quot;d0c8cbf56b61c99517936207d280de0c&quot;: &quot;treatment&quot;}}, {&quot;status&quot;: &quot;Running&quot;, &quot;audienceIds&quot;: [], &quot;variations&quot;: [{&quot;variables&quot;: [], &quot;id&quot;: &quot;20233300304&quot;, &quot;key&quot;: &quot;launch_code_variation&quot;}, {&quot;variables&quot;: [], &quot;id&quot;: &quot;20227370325&quot;, &quot;key&quot;: &quot;control&quot;}], &quot;id&quot;: &quot;20206000276&quot;, &quot;key&quot;: &quot;launch_code_verification&quot;, &quot;layerId&quot;: &quot;20233240262&quot;, &quot;trafficAllocation&quot;: [{&quot;entityId&quot;: &quot;20233300304&quot;, &quot;endOfRange&quot;: 5000}, {&quot;entityId&quot;: &quot;20233300304&quot;, &quot;endOfRange&quot;: 10000}], &quot;forcedVariations&quot;: {}}], &quot;audiences&quot;: [{&quot;conditions&quot;: &quot;[\&quot;or\&quot;, {\&quot;match\&quot;: \&quot;exact\&quot;, \&quot;name\&quot;: \&quot;$opt_dummy_attribute\&quot;, \&quot;type\&quot;: \&quot;custom_attribute\&quot;, \&quot;value\&quot;: \&quot;$opt_dummy_value\&quot;}]&quot;, &quot;id&quot;: &quot;$opt_dummy_audience&quot;, &quot;name&quot;: &quot;Optimizely-Generated Audience for Backwards Compatibility&quot;}], &quot;groups&quot;: [], &quot;attributes&quot;: [{&quot;id&quot;: &quot;16822470375&quot;, &quot;key&quot;: &quot;user_id&quot;}, {&quot;id&quot;: &quot;17143601254&quot;, &quot;key&quot;: &quot;spammy&quot;}, {&quot;id&quot;: &quot;18175660309&quot;, &quot;key&quot;: &quot;organization_plan&quot;}, {&quot;id&quot;: &quot;18813001570&quot;, &quot;key&quot;: &quot;is_logged_in&quot;}, {&quot;id&quot;: &quot;19073851829&quot;, &quot;key&quot;: &quot;geo&quot;}, {&quot;id&quot;: &quot;20175462351&quot;, &quot;key&quot;: &quot;requestedCurrency&quot;}], &quot;botFiltering&quot;: false, &quot;accountId&quot;: &quot;16737760170&quot;, &quot;events&quot;: [{&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;17911811441&quot;, &quot;key&quot;: &quot;hydro_click.dashboard.teacher_toolbox_cta&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18124116703&quot;, &quot;key&quot;: &quot;submit.organizations.complete_sign_up&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18145892387&quot;, &quot;key&quot;: &quot;no_metric.tracked_outside_of_optimizely&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18178755568&quot;, &quot;key&quot;: &quot;click.org_onboarding_checklist.add_repo&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18180553241&quot;, &quot;key&quot;: &quot;submit.repository_imports.create&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18186103728&quot;, &quot;key&quot;: &quot;click.help.learn_more_about_repository_creation&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18188530140&quot;, &quot;key&quot;: &quot;test_event.do_not_use_in_production&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18191963644&quot;, &quot;key&quot;: &quot;click.empty_org_repo_cta.transfer_repository&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18195612788&quot;, &quot;key&quot;: &quot;click.empty_org_repo_cta.import_repository&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18210945499&quot;, &quot;key&quot;: &quot;click.org_onboarding_checklist.invite_members&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18211063248&quot;, &quot;key&quot;: &quot;click.empty_org_repo_cta.create_repository&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18215721889&quot;, &quot;key&quot;: &quot;click.org_onboarding_checklist.update_profile&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18224360785&quot;, &quot;key&quot;: &quot;click.org_onboarding_checklist.dismiss&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18234832286&quot;, &quot;key&quot;: &quot;submit.organization_activation.complete&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18252392383&quot;, &quot;key&quot;: &quot;submit.org_repository.create&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18257551537&quot;, &quot;key&quot;: &quot;submit.org_member_invitation.create&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18259522260&quot;, &quot;key&quot;: &quot;submit.organization_profile.update&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18564603625&quot;, &quot;key&quot;: &quot;view.classroom_select_organization&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18568612016&quot;, &quot;key&quot;: &quot;click.classroom_sign_in_click&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18572592540&quot;, &quot;key&quot;: &quot;view.classroom_name&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18574203855&quot;, &quot;key&quot;: &quot;click.classroom_create_organization&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18582053415&quot;, &quot;key&quot;: &quot;click.classroom_select_organization&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18589463420&quot;, &quot;key&quot;: &quot;click.classroom_create_classroom&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18591323364&quot;, &quot;key&quot;: &quot;click.classroom_create_first_classroom&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18591652321&quot;, &quot;key&quot;: &quot;click.classroom_grant_access&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;18607131425&quot;, &quot;key&quot;: &quot;view.classroom_creation&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;18831680583&quot;, &quot;key&quot;: &quot;upgrade_account_plan&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19064064515&quot;, &quot;key&quot;: &quot;click.signup&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19075373687&quot;, &quot;key&quot;: &quot;click.view_account_billing_page&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19077355841&quot;, &quot;key&quot;: &quot;click.dismiss_signup_prompt&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19079713938&quot;, &quot;key&quot;: &quot;click.contact_sales&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19120963070&quot;, &quot;key&quot;: &quot;click.compare_account_plans&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19151690317&quot;, &quot;key&quot;: &quot;click.upgrade_account_cta&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19424193129&quot;, &quot;key&quot;: &quot;click.open_account_switcher&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19520330825&quot;, &quot;key&quot;: &quot;click.visit_account_profile&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19540970635&quot;, &quot;key&quot;: &quot;click.switch_account_context&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19730198868&quot;, &quot;key&quot;: &quot;submit.homepage_signup&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19820830627&quot;, &quot;key&quot;: &quot;click.homepage_signup&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;19988571001&quot;, &quot;key&quot;: &quot;click.create_enterprise_trial&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20036538294&quot;, &quot;key&quot;: &quot;click.create_organization_team&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20040653299&quot;, &quot;key&quot;: &quot;click.input_enterprise_trial_form&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20062030003&quot;, &quot;key&quot;: &quot;click.continue_with_team&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20068947153&quot;, &quot;key&quot;: &quot;click.create_organization_free&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20086636658&quot;, &quot;key&quot;: &quot;click.signup_continue.username&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20091648988&quot;, &quot;key&quot;: &quot;click.signup_continue.create_account&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20103637615&quot;, &quot;key&quot;: &quot;click.signup_continue.email&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20111574253&quot;, &quot;key&quot;: &quot;click.signup_continue.password&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20120044111&quot;, &quot;key&quot;: &quot;view.pricing_page&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20152062109&quot;, &quot;key&quot;: &quot;submit.create_account&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20165800992&quot;, &quot;key&quot;: &quot;submit.upgrade_payment_form&quot;}, {&quot;experimentIds&quot;: [], &quot;id&quot;: &quot;20171520319&quot;, &quot;key&quot;: &quot;submit.create_organization&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;20222645674&quot;, &quot;key&quot;: &quot;click.recommended_plan_in_signup.discuss_your_needs&quot;}, {&quot;experimentIds&quot;: [&quot;20206000276&quot;], &quot;id&quot;: &quot;20227443657&quot;, &quot;key&quot;: &quot;submit.verify_primary_user_email&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;20234607160&quot;, &quot;key&quot;: &quot;click.recommended_plan_in_signup.try_enterprise&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;20238175784&quot;, &quot;key&quot;: &quot;click.recommended_plan_in_signup.team&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;20239847212&quot;, &quot;key&quot;: &quot;click.recommended_plan_in_signup.continue_free&quot;}, {&quot;experimentIds&quot;: [&quot;20194668672&quot;], &quot;id&quot;: &quot;20251097193&quot;, &quot;key&quot;: &quot;recommended_plan&quot;}], &quot;revision&quot;: &quot;696&quot;}">
<!-- To prevent page flashing, the optimizely JS needs to be loaded in the
    <head> tag before the DOM renders -->
<script crossorigin="anonymous" defer="defer"
	integrity="sha512-yDmmCGyENqEePvF9X9A4omxWCNcbS6qK2h8HZPdnvXd02Vzhtqd0zRd/pgTgqQ/xOA02F3H225VpJvDXrnfNbA=="
	type="application/javascript"
	src="https://github.githubassets.com/assets/optimizely-c839a608.js"></script>





<meta name="hostname" content="github.com">
<meta name="user-login" content="">


<meta name="expected-hostname" content="github.com">


<meta name="enabled-features"
	content="MARKETPLACE_PENDING_INSTALLATIONS,AUTOCOMPLETE_EMOJIS_IN_MARKDOWN_EDITOR">

<meta http-equiv="x-pjax-version"
	content="4e770257ffcdcd15365ee5885252e58c0fcd874efe3c34b9f55301e30e1d1549">


<link crossorigin="anonymous" media="all"
	integrity="sha512-cf8Vh7kAWS+7gVS00gNqLJTzqbYA5C5pQAe+zQ9hC39imrLnjUjGoSlqZ8rQTFuQhB9QzzR4vb40P+aDfomMcg=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/site-71ff1587b900592fbb8154b4d2036a2c.css">
<link crossorigin="anonymous" media="all"
	integrity="sha512-G2YMVGnLxQUVq6IX9obVCgJdMPp+W4B3QHrxs8yFv/pqR7rXsUgRfv6iqMiOQPU9k+hOEKQB9Bnd5znxKzIahQ=="
	rel="stylesheet"
	href="https://github.githubassets.com/assets/home-1b660c5469cbc50515aba217f686d50a.css">





<meta name="browser-stats-url"
	content="https://api.github.com/_private/browser/stats">

<meta name="browser-errors-url"
	content="https://api.github.com/_private/browser/errors">

<meta name="browser-optimizely-client-errors-url"
	content="https://api.github.com/_private/browser/optimizely_client/errors">

<link rel="mask-icon" href="svg/pinned-octocat.svg" color="#000000">
<link rel="alternate icon" class="js-site-favicon" type="image/png" href="png/favicon.png">
<link rel="icon" class="js-site-favicon" type="image/svg+xml" href="svg/favicon.svg">

<meta name="theme-color" content="#1e2327">
<meta name="color-scheme" content="light dark">


<link rel="manifest" href="manifest.json" crossorigin="use-credentials">

<meta name="enabled-homepage-translation-languages" content="">

</head>

<body
	class="logged-out env-production page-responsive height-full d-flex flex-column header-overlay intent-mouse"
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



		<header class="header-logged-out f4 py-3 z-2" role="banner">
			<div class="container-xl d-lg-flex flex-items-center p-responsive">
				<div
					class="d-flex flex-justify-between flex-items-center width-full">
					<a href="https://github.com/" aria-label="Homepage"> <svg
							aria-hidden="true" viewBox="0 0 16 16" version="1.1"
							data-view-component="true" height="32" width="32"
							class="octicon octicon-mark-github color-text-white">
    <path fill-rule="evenodd"
								d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27.68 0 1.36.09 2 .27 1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.013 8.013 0 0016 8c0-4.42-3.58-8-8-8z"></path>
</svg>
					</a>

					<div class="font-mktg">
						<span class="mr-2 text-gray-mktg"><?php echo $alreadyExists?></span>
						<a href="login.php?lang=<?php echo $lang?>" class="color-text-white"> <?php echo $signIn?> →</a>
					</div>
				</div>
			</div>
		</header>


	</div>

	<div id="start-of-content" class="show-on-focus"></div>





	<include-fragment class="js-notification-shelf-include-fragment"
		data-base-src="https://github.com/notifications/beta/shelf"></include-fragment>




	<div class="application-main d-flex flex-auto flex-column"
		data-commit-hovercards-enabled=""
		data-discussion-hovercards-enabled=""
		data-issue-and-pr-hovercards-enabled="">
		<main
			class="bg-gray-dark-mktg d-flex flex-auto flex-column overflow-hidden position-relative">
			<div>
				<div class="signup-bg-stars"></div>
				<div class="signup-bg-stars-2"></div>
				<div class="signup-bg-stars-3"></div>
			</div>
			<div class="d-flex flex-auto flex-justify-center pt-12">

				<text-suggester
					class="js-continue-container width-full z-1 signup-text-suggester"
					data-catalyst="">
				<div
					class="m-4 p-4 f4 color-shadow-small bg-gray-800-mktg rounded-2 signup-content-container">
					<h1 class="sr-only">Welcome to Github! Let's begin the adventure</h1>					
					<typing-effect
						data-lines="<?php echo $typingEffect?>"
						data-continue-to="email-container" class="js-signup-typed-welcome">
						  
					<span data-target="typing-effect.content" class="text-mono text-gray-mktg"></span>
					<span data-target="typing-effect.cursor"
						class="typing-effect-cursor" hidden="">|</span> </typing-effect>

					<noscript>
						<div class="my-4 text-mono color-text-warning">GitHub requires
							JavaScript enabled to sign up for our captcha. Please enable
							JavaScript.</div>
					</noscript>

					<form class="position-relative js-octocaptcha-parent"
						action="/signup" accept-charset="UTF-8" method="post">
						<input type="hidden" data-csrf="true" name="authenticity_token"
							value="i4o4EkxwhIOu4A/InJX3fzUr9s5oY9WdjsGj3M7s5Tp0rUj/+PLsLLgxFHXpxiC90X4oeznv5oekbexmLlJjsQ==">
						<div id="email-container"
							class="js-continue-step-container signup-continue-step-container mt-4"
							data-step-state="active">
							<div>
								<label for="email" class="text-mono signup-text-prompt"> <?php echo $enterEmail?><span class="sr-only">e.g. monalisa@github.com</span>
								</label>
							</div>
							<div class="d-flex flex-items-center flex-column flex-sm-row">
								<div class="d-flex flex-items-center width-full">
									<span class="signup-continue-prompt mr-2" aria-hidden="true"></span>
									<auto-check src="email_validity_checks"
										class="js-prevent-default-behavior width-full" required=""> <input
										id="email"
										class="js-continue-input js-continue-focus-target signup-input form-control input-block flex-1 border-0 rounded-0 p-0 box-shadow-none color-text-white f4 text-mono"
										required="" autofocus="autofocus" autocomplete="off"
										data-target="text-suggester.input"
										aria-describedby="email-err" type="email" name="user[email]"
										spellcheck="false"> <input type="hidden" data-csrf="true"
										value="zR3WngS4xo3KNTK+jiy9zMvvRgkaMkPaWBrZqnGVXChfI0Qnttkfy1PgmnAST6UQXGk70E1Trgo+kXKhmKSxhA==">
									</auto-check>
								</div>
								<button type="button"
									data-optimizely-event="click.signup_continue.email"									
									data-continue-to="password-container"
									style="width:<?php echo $buttonWidth?>"><?php echo $continue?></button>
							</div>
						</div>

						<div id="password-container"
							class="js-continue-step-container signup-continue-step-container"
							hidden="" data-step-state="invalid">
							<div class="mt-4">
								<label for="password" class="text-mono signup-text-prompt">
									Create a password </label>
							</div>
							<div class="d-flex flex-items-center flex-column flex-sm-row">
								<div class="d-flex flex-items-center width-full">
									<span class="signup-continue-prompt mr-2" aria-hidden="true"></span>
									<visible-password class="flex-1 d-flex flex-items-center mr-3"
										data-catalyst=""> <auto-check src="password_validity_checks"
										class="js-prevent-default-behavior flex-1" required=""> <input
										id="password"
										class="form-control js-continue-input js-continue-focus-target signup-input form-control input-block flex-1 border-0 rounded-0 p-0 box-shadow-none color-text-white f4 text-mono"
										required="" autocomplete="off"
										data-target="visible-password.input"
										aria-describedby="password-err" type="password"
										name="user[password]" spellcheck="false"> <input type="hidden"
										data-csrf="true"
										value="VkKFSscfEV2F6RrM2TmOG/WGShfu39k2mPcagOLpc1Xl1JTkOWB9UiOkcev+D46FG3fk/peg6A/Vp9kccv1u1w==">
									</auto-check>
									<button type="button"
										class="btn-link signup-password-visibility-toggle"
										data-target="visible-password.showButton"
										data-action="click:visible-password#show">
										<svg aria-hidden="true" viewBox="0 0 16 16" version="1.1"
											data-view-component="true" height="16" width="16"
											class="octicon octicon-eye">
    <path fill-rule="evenodd"
												d="M1.679 7.932c.412-.621 1.242-1.75 2.366-2.717C5.175 4.242 6.527 3.5 8 3.5c1.473 0 2.824.742 3.955 1.715 1.124.967 1.954 2.096 2.366 2.717a.119.119 0 010 .136c-.412.621-1.242 1.75-2.366 2.717C10.825 11.758 9.473 12.5 8 12.5c-1.473 0-2.824-.742-3.955-1.715C2.92 9.818 2.09 8.69 1.679 8.068a.119.119 0 010-.136zM8 2c-1.981 0-3.67.992-4.933 2.078C1.797 5.169.88 6.423.43 7.1a1.619 1.619 0 000 1.798c.45.678 1.367 1.932 2.637 3.024C4.329 13.008 6.019 14 8 14c1.981 0 3.67-.992 4.933-2.078 1.27-1.091 2.187-2.345 2.637-3.023a1.619 1.619 0 000-1.798c-.45-.678-1.367-1.932-2.637-3.023C11.671 2.992 9.981 2 8 2zm0 8a2 2 0 100-4 2 2 0 000 4z"></path>
</svg>
									</button>
									<button type="button"
										class="btn-link signup-password-visibility-toggle"
										data-target="visible-password.hideButton"
										data-action="click:visible-password#hide" hidden="">
										<svg aria-hidden="true" viewBox="0 0 16 16" version="1.1"
											data-view-component="true" height="16" width="16"
											class="octicon octicon-eye-closed">
    <path fill-rule="evenodd"
												d="M.143 2.31a.75.75 0 011.047-.167l14.5 10.5a.75.75 0 11-.88 1.214l-2.248-1.628C11.346 13.19 9.792 14 8 14c-1.981 0-3.67-.992-4.933-2.078C1.797 10.832.88 9.577.43 8.9a1.618 1.618 0 010-1.797c.353-.533.995-1.42 1.868-2.305L.31 3.357A.75.75 0 01.143 2.31zm3.386 3.378a14.21 14.21 0 00-1.85 2.244.12.12 0 00-.022.068c0 .021.006.045.022.068.412.621 1.242 1.75 2.366 2.717C5.175 11.758 6.527 12.5 8 12.5c1.195 0 2.31-.488 3.29-1.191L9.063 9.695A2 2 0 016.058 7.52l-2.53-1.832zM8 3.5c-.516 0-1.017.09-1.499.251a.75.75 0 11-.473-1.423A6.23 6.23 0 018 2c1.981 0 3.67.992 4.933 2.078 1.27 1.091 2.187 2.345 2.637 3.023a1.619 1.619 0 010 1.798c-.11.166-.248.365-.41.587a.75.75 0 11-1.21-.887c.148-.201.272-.382.371-.53a.119.119 0 000-.137c-.412-.621-1.242-1.75-2.366-2.717C10.825 4.242 9.473 3.5 8 3.5z"></path>
</svg>
									</button>
									</visible-password>
								</div>
								<button type="button"
									data-optimizely-event="click.signup_continue.password"									
									data-continue-to="username-container" disabled=""
									style="width:<?php echo $buttonWidth?>"><?php echo $continue?></button>
							</div>
						</div>

						<div id="username-container"
							class="js-continue-step-container signup-continue-step-container"
							hidden="" data-step-state="invalid">
							<div class="mt-4">
								<label for="login" class="text-mono signup-text-prompt"> Enter a
									username </label>
							</div>
							<div class="d-flex flex-items-center flex-column flex-sm-row">
								<div class="d-flex flex-items-center width-full">
									<span class="signup-continue-prompt mr-2" aria-hidden="true"></span>
									<auto-check src="signup_check_username"
										class="js-prevent-default-behavior width-full" required=""> <input
										id="login"
										class="form-control js-continue-input js-continue-focus-target signup-input form-control input-block flex-1 border-0 rounded-0 p-0 box-shadow-none color-text-white f4 text-mono"
										required="" autocomplete="off" aria-describedby="login-err"
										type="text" name="user[login]" spellcheck="false"> <input
										type="hidden" data-csrf="true"
										value="DHyuTCr58hAL3rZY8gFgy0ApmEp0mgbVXMZ0I5DDHSz9jX/qFoMS/NztshNDpyC6IbcqEfvFR/YZfaBMTCk2Jg==">
									</auto-check>
								</div>
								<button type="button"
									data-continue-to="opt-in-container"
									data-optimizely-event="click.signup_continue.username"
									style="width:<?php echo $buttonWidth?>"><?php echo $continue?></button>
							</div>
						</div>

						<div id="opt-in-container"
							class="js-continue-step-container signup-continue-step-container"
							hidden="" data-step-state="complete">
							<div class="mt-4 mb-2">
								<label for="opt-in" class="text-mono signup-text-prompt"> Would
									you like to receive product updates and announcements via
									email?<br> Type "y" for yes or "n" for no
								</label>
							</div>
							<div class="d-flex flex-items-center flex-column flex-sm-row">
								<div class="d-flex flex-items-center width-full">
									<span class="signup-continue-prompt mr-2"></span> <input
										type="text" name="opt_in" id="opt_in" value=""
										class="form-control js-continue-input js-continue-focus-target signup-input form-control input-block flex-1 border-0 rounded-0 p-0 box-shadow-none color-text-white f4 text-mono">
								</div>
								<button type="button"									
									data-continue-to="captcha-and-submit-container"
									data-optimizely-event="click.signup_continue.opt-in"
									style="width:<?php echo $buttonWidth?>"><?php echo $continue?></button>
							</div>
						</div>

						<div id="captcha-and-submit-container"
							class="width-full js-continue-step-container captcha-container"
							data-step-state="complete" hidden=""
							style="position: relative; top: 0px;">
							<div class="text-mono text-bold signup-text-prompt mt-4">Verify
								your account</div>
							<div class="js-continue-focus-target" tabindex="-1"
								style="outline: none;">

								<div class="my-3">
									<div
										class="js-octocaptcha-spinner d-flex flex-justify-center flex-items-center width-full d-none">
										<img alt="Waiting for verification." src="gif/octocat-spinner-128.gif" width="64" height="64">
									</div>

									<div
										class="js-octocaptcha-success d-none d-flex flex-justify-center flex-items-center width-full">
										<svg height="64"
											class="octicon octicon-check color-text-success"
											aria-label="Account has been verified. Please continue."
											viewBox="0 0 24 24" version="1.1" width="64" role="img">
											<path fill-rule="evenodd"
												d="M21.03 5.72a.75.75 0 010 1.06l-11.5 11.5a.75.75 0 01-1.072-.012l-5.5-5.75a.75.75 0 111.084-1.036l4.97 5.195L19.97 5.72a.75.75 0 011.06 0z"></path></svg>
									</div>
								</div>

							</div>

							<input class="form-control" type="text"
								name="required_field_07fe" hidden="hidden"> <input
								class="form-control" type="hidden" name="timestamp"
								value="1624000631706"> <input class="form-control" type="hidden"
								name="timestamp_secret"
								value="2206fc343c99c7b6c52524e285d3f52fcdb03cc032aa22ebeef5b4f926c8d4b0">


							<button name="button" type="submit"
								class="form-control signup-submit-button width-full py-2 js-octocaptcha-form-submit"
								data-optimizely-event="click.signup_continue.create_account"
								data-disable-invalid="true" disabled="" hidden="hidden">Create
								account</button>
						</div>
					</form>
				</div>
				<div
					class="js-continue-hint-container mx-4 px-4 f4 font-mktg text-gray-mktg">
					<p id="email-err" data-hint-for="email" role="alert"
						aria-atomic="true"></p>
					<p id="password-err" data-hint-for="password" role="alert"
						aria-atomic="true" hidden=""></p>
					<p id="login-err" data-hint-for="login" role="alert"
						aria-atomic="true" hidden=""></p>
				</div>
				</text-suggester>

			</div>

			<img src="svg/hero-glow.svg" alt="Glowing universe" class="position-absolute overflow-hidden home-hero-glow events-none">
		</main>

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