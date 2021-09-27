<template>
	<div tabindex=1 class=contents @keydown=keydown>
		<search-form v-if=issearch></search-form>
		<packages ref=packages :packages=packages></packages>
		<br>
		<hr>
		<theorems ref=theorems :theorems=theorems :initial-index="packages.length + 1"></theorems>
	</div>
</template>

<script>
console.log('importing axiomContents.vue');
import packages from "./packages.vue"
import theorems from "./theorems.vue"
import searchForm from "./searchForm.vue"

export default {		
	components : {packages, theorems, searchForm},		
	
	props : [ 'packages', 'theorems' ],

	data(){
		return {
			issearch: false,
		};		
	},
	
	methods: {
		keydown(event){
			switch(event.key){
			case 'F':
			case 'f':
				if (event.ctrlKey){
					this.issearch = true;
					event.preventDefault();
				}
			}
		},			
	},
	
	mounted(){
		if (this.theorems){
			var hash = location.hash;			
			if (hash){
				hash = hash.slice(1);
			}
			
			this.$refs.theorems.focus(hash);
		}
		else if (this.packages){
			this.$refs.packages.focus();
		}			
	},
}
</script>

<style scoped>
.contents {
	margin-left: 2em;
}
</style>