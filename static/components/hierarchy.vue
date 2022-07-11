<template>
	<div>
		<hierarchyInformation :key-input=keyInput :deep="!deep"></hierarchyInformation>
		<br>
		<hierarchyModule ref=hierarchyModule :module=module></hierarchyModule>			
	</div>
</template>

<script>
console.log('importing hierarchy.vue');	

import hierarchyInformation from "./hierarchyInformation.vue"
import hierarchyModule from "./hierarchyModule.vue"

export default {
	components: {hierarchyModule, hierarchyInformation },
	
	props : [ 'module', 'graph', 'traceback', 'keyInput'],

	computed: {
		deep(){
			var hash = location.hash;			
			if (hash){
				hash = hash.slice(1);
				if (hash == 'deep')
					return true;
			}
			return false;
		},
	},
	
	methods: {
	},
	
	mounted(){
		var hierarchyModule = this.$refs.hierarchyModule;
		if (this.deep){
			hierarchyModule.deep = true;
		}
		else{
			hierarchyModule.show = true;	
		}
	},
};
</script>

<style>
</style>