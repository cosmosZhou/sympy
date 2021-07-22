<template>
	<small-icon class=small-package :text=package :lines=2></small-icon>
</template>

<script>
	console.log('importing small-package.vue');
	var smallIcon = httpVueLoader('static/vue/small-icon.vue');
	module.exports = {
		components: {smallIcon},
		
		props : ['package'],
		
		methods : {
			dblclick(event) {
				//console.log("dblclick(event) { in small-package.vue");
				var parent = this.$parent;
				parent.path += "/" + this.package;
				parent.fucus();
			},
		}
	}
</script>

<style>

.small-package {
	width: 2.5em;
	height: 1.5em;
	margin: 25px auto;
	position: relative;
	height: 1.5em;
	z-index: 1;
}

div .small-package {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 0.8em;
	background: rgb(220, 220, 0);
	border-top-left-radius: 0.15em;
	border-top-right-radius: 0.15em;
}

.small-package:before {
	width: 1.5em;
	height: 0.5em;
	position: absolute;
	left: 0.15em;
	top: -0.35em;
	content: "";
	background: rgb(220, 180, 0);
	border-top-left-radius: 0.15em;
	border-top-right-radius: 0.15em;
	box-shadow: 0.1em 0.1em 0 0 #9da0a0;
	z-index: 0;
}

.small-package:after {
	position: absolute;
	content: "";
}

</style>