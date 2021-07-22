<template>
	<div>
		<hierarchy-information :key-input=keyInput :deep="!deep"></hierarchy-information>
		<br>
		<hierarchy-module ref=module :module=module :show=true></hierarchy-module>			
	</div>
</template>

<script>
	console.log('importing hierarchy.vue');	

	var	hierarchyInformation = httpVueLoader('static/vue/hierarchy-information.vue');
    var	hierarchyModule = httpVueLoader('static/vue/hierarchy-module.vue');    

	module.exports = {
		components: {hierarchyModule, hierarchyInformation },
		
		props : [ 'module', 'graph', 'traceback', 'keyInput', 'deep' ],

		methods: {			
		},
	};
</script>

<style>
</style>