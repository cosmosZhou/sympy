<template>
	<div tabindex=1 class=contents @keydown=keydown>
		<searchForm v-if="issearch" :keyword=keyword :caseSensitive=caseSensitive :wholeWord=wholeWord :regularExpression=regularExpression :nlp=nlp></searchForm>
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
			
			keyword: '',
			caseSensitive: false,
			wholeWord: false, 
			regularExpression: false,
			nlp: false,			
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
		var hash = location.hash;			
		if (hash){
			hash = hash.slice(1);
		}
		
		var hit = false;
		if (this.theorems.length){
			hit = this.$refs.theorems.focus(hash);
		}
		
		if (!hit && this.packages.length){
			this.$refs.packages.focus(hash);
		}			
	},
}
</script>

<style scoped>
.contents {
	margin-left: 2em;
}
</style>