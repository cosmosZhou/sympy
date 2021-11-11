<template>
	<div>
		<hierarchyInformation :key-input=keyInput :deep="!deep"></hierarchyInformation>
		<br>
		<hierarchyModule ref=module :module=module :show=true></hierarchyModule>			
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