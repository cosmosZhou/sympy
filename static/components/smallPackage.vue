<template>
	<smallIcon class=smallPackage :text=package :lines=2></smallIcon>
</template>

<script>
console.log('importing smallPackage.vue');
import smallIcon from "./smallIcon.vue"
export default {
	components: {smallIcon},
	
	props : ['package'],
	
	methods : {
		dblclick(event) {
			var parent = this.$parent;
			parent.path += "/" + this.package;
			parent.fucus();
		},
	}
}
</script>

<style>

.smallPackage {
	width: 2.5em;
	height: 1.5em;
	margin: 25px auto;
	position: relative;
	height: 1.5em;
	z-index: 1;
}

div .smallPackage {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 0.8em;
	background: rgb(220, 220, 0);
	border-top-left-radius: 0.15em;
	border-top-right-radius: 0.15em;
}

.smallPackage:before {
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

.smallPackage:after {
	position: absolute;
	content: "";
}

</style>