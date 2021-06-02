<template>
	<div>
		packages:<br>  
		<template v-for="package, i of packages">
			<package :package=package :tabindex="i + 1"></package>
			<contextmenu v-if='i == focusedIndex' :left=left :top=top></contextmenu>
		</template>
		
	</div>

</template>

<script>
	console.log('importing packages.vue');	
	var package = httpVueLoader('/sympy/vue/package.vue');
	var contextmenu = httpVueLoader('/sympy/vue/contextmenu.vue');
	module.exports = {		
		data(){
			return {
				focusedIndex: -1,
				left: 0,
				top: 0,
			};
		},
		
		components : {package, contextmenu},
	
		props : [ 'packages'],
		
		methods: {

			remove(indexFocused){
				var packages = this.packages;
				packages.remove(indexFocused);
				this.packages = packages;
				
				this.$nextTick(function() {				
					// Code that will run only after the entire view has been rendered
					var index = indexFocused;
					var self = this;
					if (index == this.$children.length){
						--index;
						if(index < 0){
							var forefather = this.$parent;
							self = forefather.$children[1];
							index = 0;							
						}
					}
					 
					self.$children[index].$el.focus();
					
				});				
			},
		}
	};
</script>

<style>
</style>