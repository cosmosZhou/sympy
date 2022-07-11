<template>
	<div>
		packages:<br>  
		<template v-for="module, i of packages">
			<axiomPackage :module=module :tabindex="i + 1" :index=i></axiomPackage>
			<axiomContextmenu v-if='i == focusedIndex' :left=left :top=top></axiomContextmenu>
		</template>
		
	</div>
</template>

<script>
console.log('importing packages.vue');	
import axiomPackage from "./axiomPackage.vue"
import axiomContextmenu from "./axiomContextmenu.vue"
export default {
	components : {axiomPackage, axiomContextmenu},
	
	data(){
		return {
			focusedIndex: -1,
			left: 0,
			top: 0,
			axiomPackage: [],
		};
	},

	props : [ 'packages'],
	
	computed: {
		children(){
			return this.axiomPackage;
		},

		focusedElement(){
			return this.axiomPackage[this.focusedIndex];
		},		
	},
	
	methods: {
		indexOf(element){
			return this.packages.indexOf(element.module);	
		},
		
		focus(hash){
			if (hash){
				for (let el of this.$el.querySelectorAll(".package")){
					if (el.textContent.trim() == hash){
						el.focus();
						return true;
					}
				}
			}

			var el = this.$el.querySelector(".package");
			el.focus();
		},

		remove(indexFocused){
			var packages = this.packages;
			packages.remove(indexFocused);
			this.packages = packages;
			
			this.$nextTick(function() {				
				// Code that will run only after the entire view has been rendered
				var index = indexFocused;
				var self = this;
				if (index == this.children.length){
					--index;
					if(index < 0){
						var forefather = this.$parent;
						self = forefather.children[1];
						index = 0;							
					}
				}
				 
				self.children[index].$el.focus();
				
			});				
		},
	}
}
</script>

<style>
</style>