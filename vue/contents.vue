<template>
	<div class=contents>
		<packages :packages=packages></packages>
		<br>		
		<hr>		
		<theorems :theorems=theorems :initial-index="packages.length + 1"></theorems>
	</div>
</template>

<script>
	console.log('importing contents.vue');
	var packages = httpVueLoader('/sympy/vue/packages.vue');
	var theorems = httpVueLoader('/sympy/vue/theorems.vue');
	module.exports = {		
		components : {packages, theorems,},		
		
		props : [ 'packages', 'theorems' ],

		methods: {
		},		
	};
</script>

<style scoped>
.contents {
	margin-left: 2em;
}
</style>