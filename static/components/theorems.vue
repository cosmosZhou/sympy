<template>
	<div>
		theorems:<br>
		<template v-for="theorem, i of theorems">
			<axiomTheorem :theorem=theorem :tabindex="i + initialIndex" :index=i></axiomTheorem>
			<template v-if='i == focusedIndex'>
				<axiomContextmenu v-if='left >= 0' :left=left :top=top></axiomContextmenu>
				<packageSelector v-else :path=path></packageSelector>				
			</template>
		</template>		
	</div>
</template>

<script>
console.log('importing theorems.vue');	

import axiomTheorem from "./axiomTheorem.vue"
import axiomContextmenu from "./axiomContextmenu.vue"
import packageSelector from "./packageSelector.vue"
export default {
	data(){
		return {
			focusedIndex: -1,
			left: -1,
			top: -1,
			axiomTheorem: [],
		};
	},
	
	components : {axiomTheorem, axiomContextmenu, packageSelector},

	props : [ 'theorems', 'initialIndex' ],

	computed :{
		children(){
			return this.axiomTheorem;
		},
		
		path(){
			var href = location.href;
			return href.match(/\/axiom\.php\?module=((?:\w+[.\/])+)(\w+)[.\/]?(?:#\w+)?$/)[1];
			//return href.match(/\/axiom.php(\/.*)\/(\w+)\/*$/)[1];
		},
		
		focusedElement(){
			return this.axiomTheorem[this.focusedIndex];
		},
	},
	
	methods: {
		
		indexOf(element){
			return this.theorems.indexOf(element.theorem);	
		},
		
		focus(hash){
			if (hash){
				for (let el of this.$el.querySelectorAll(".theorem")){
					if (el.textContent.trim() == hash){
						el.focus();
						return true;
					}
				}
			}
			var el = this.$el.querySelector(".theorem");
			el.focus();
		},
		
		remove(indexFocused){
			console.log("theorems = " + this.theorems);
			var theorems = this.theorems;
			theorems.remove(indexFocused);
			this.theorems = theorems;
			
			this.$nextTick(function() {				
				// Code that will run only after the entire view has been rendered
				var index = indexFocused;
				var self = this;
				if (index == this.children.length){
					--index;
					if(index < 0){
						var forefather = this.$parent;
						var self = forefather.children[0];
						index = self.children.length - 1;							
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