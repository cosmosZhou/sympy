<template>
	<div>
		<hierarchy-information :key-input=keyInput :deep="!deep"></hierarchy-information>
		<br>
		<hierarchy-module ref=module :module=module :show=true></hierarchy-module>			
	</div>
</template>

<script>
	console.log('importing hierarchy.vue');	

	var	hierarchyInformation = httpVueLoader('/sympy/vue/hierarchy-information.vue');
	var	hierarchyHref = httpVueLoader('/sympy/vue/hierarchy-href.vue');
    var	hierarchyModule = httpVueLoader('/sympy/vue/hierarchy-module.vue');

	module.exports = {
		components: {hierarchyModule, hierarchyHref, hierarchyInformation },
		
		props : [ 'module', 'graph', 'traceback', 'keyInput', 'deep' ],

		methods: {			
		},
	};
</script>

<style>
</style>