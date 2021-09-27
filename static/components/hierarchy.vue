<template>
	<div>
		<hierarchy-information :key-input=keyInput :deep="!deep"></hierarchy-information>
		<br>
		<hierarchy-module ref=module :module=module :show=true></hierarchy-module>			
	</div>
</template>

<script>
	console.log('importing hierarchy.vue');	

	import hierarchyInformation from "./hierarchyInformation.vue"
    import hierarchyModule from "./hierarchyModule.vue"

	export default {
		components: {hierarchyModule, hierarchyInformation },
		
		props : [ 'module', 'graph', 'traceback', 'keyInput', 'deep' ],

		methods: {			
		},
	};
</script>

<style>
</style>