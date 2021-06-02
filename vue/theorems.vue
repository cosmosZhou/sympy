<template>
	<div>
		theorems:<br>
		<template v-for="theorem, i of theorems">
			<theorem :theorem=theorem :tabindex="i + initialIndex"></theorem>
			<template v-if='i == focusedIndex'>
				<contextmenu v-if='left >= 0' :left=left :top=top></contextmenu>
				<package-selector v-else :path=path></package-selector>				
			</template>
		</template>		
	</div>

</template>

<script>
	console.log('importing theorems.vue');	

	var theorem = httpVueLoader('/sympy/vue/theorem.vue');
	var contextmenu = httpVueLoader('/sympy/vue/contextmenu.vue');
	var packageSelector = httpVueLoader('/sympy/vue/package-selector.vue');
	module.exports = {
		data(){
			return {
				focusedIndex: -1,
				left: -1,
				top: -1,
			};
		},
		
		components : {theorem, contextmenu, packageSelector},
	
		props : [ 'theorems', 'initialIndex' ],

		computed :{
			path(){
				var href = location.href;				
				return href.match(/\/axiom.php(\/.*)\/(\w+)\/*$/)[1];
			},
		},
		
		methods: {
			
			remove(indexFocused){
				console.log("theorems = " + this.theorems);
				var theorems = this.theorems;
				theorems.remove(indexFocused);
				this.theorems = theorems;
				
				this.$nextTick(function() {				
					// Code that will run only after the entire view has been rendered
					var index = indexFocused;
					var self = this;
					if (index == this.$children.length){
						--index;
						if(index < 0){
							var forefather = this.$parent;
							var self = forefather.$children[0];
							index = self.$children.length - 1;							
						}
					}
					 
					self.$children[index].$el.focus();					
				});				
			},
		}

		
	}
</script>

<style>
</style>