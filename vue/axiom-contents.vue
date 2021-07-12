<template>
	<div tabindex=1 class=contents @keydown=keydown>
		<search-form v-if=issearch></search-form>
		<packages :packages=packages></packages>
		<br>
		<hr>
		<theorems :theorems=theorems :initial-index="packages.length + 1"></theorems>
	</div>
</template>

<script>
	console.log('importing axiom-contents.vue');
	var packages = httpVueLoader('/sympy/vue/packages.vue');
	var theorems = httpVueLoader('/sympy/vue/theorems.vue');
	var searchForm = httpVueLoader('/sympy/vue/search-form.vue');
	module.exports = {		
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
				case 'f':
					if (event.ctrlKey){
						this.issearch = true;
						event.preventDefault();
						
						this.$nextTick(()=>{
							promise(()=>{
								$("input[type=text]")[0].focus();
							});
						});
					}
				}
			},			
		},		
	};
</script>

<style scoped>
.contents {
	margin-left: 2em;
}
</style>