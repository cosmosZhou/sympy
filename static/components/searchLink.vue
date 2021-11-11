<template>
	<input v-if="mode != 'a'" v-focus spellcheck=false :size='module.length + 1' :value=module @blur=blur @keydown=keydown>
	<a v-else v-focus tabindex=2 :href=href @contextmenu.prevent=contextmenu @keydown=keydown_a>
       	{{module}}
       	<search-contextmenu v-if='showContextmenu' :left=left :top=top></search-contextmenu>
    </a>
</template>

<script>
console.log('importing searchLink.vue');
import searchContextmenu from "./searchContextmenu.vue"

var focusedAlready = false;
export default {
	components: {searchContextmenu},
	
	data(){
		return {
			mode: 'a',
			showContextmenu: false,
			left: -1,
			top: -1,
		};
	},
	
	props: ['module'],
	
	computed: {
		user(){
			return sympy_user();
		},
		
		href(){
			return `/${this.user}/axiom.php?module=${this.module}`;
		},			
	},
	
	methods: {
		set_module(module){
			if (this.module == module){
				return;	
			}

			console.log('oldText = ' + this.module);
			console.log('newText = ' + module);			
			
			var sympy = sympy_user();
			
			form_post(`php/request/rename.php`, { old: this.module, new: module}).then(res => {
				console.log('res = ' + res);					
			});
			
			var modules = this.$root.modules;
			if (!modules){
				console.assert(this.module == this.$root.module, "this.module == this.$root.module");
				this.$root.graph[module] = this.$root.graph[this.module];
				delete this.$root.graph[this.module];
				this.$root.module = module;
			}
			else{
				modules[modules.indexOf(this.module)] = module;	
			}
		},
		
		contextmenu(event) {
			//console.log("contextmenu: function(event)");
			var self = event.target;				
			
			this.left = event.x + self.getScrollLeft();
			this.top = event.y + self.getScrollTop();
			
			this.showContextmenu = true;
			
			setTimeout(()=>{
				var contextmenu = self.lastElementChild;
				contextmenu.focus();				
			}, 100);				
		},
		
		blur(event){
			if (this.mode == 'F3'){
				this.mode = 'input';
			}
			else{
				this.mode = 'a';
				this.set_module(event.target.value);
			}				
		},
		
		keydown(event){
			switch(event.key){
			case 'Enter':
				this.set_module(event.target.value);
				this.mode = 'a';
				var self = this;
				setTimeout(()=>{
					self.$el.focus();				
				}, 100);
				
				break;
			case 'F3':
				console.log("F3 is pressed");
				this.mode = 'F3';
				find_and_jump(event);
				break;					
			}
		},
		
		keydown_a(event){
			switch(event.key){
			case 'F2':
				this.mode = 'input';
				focusedAlready = false;
				break;
			}				
		},
	},
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	if (!focusedAlready || el.tagName == 'input'){
		    		el.focus();
		    		focusedAlready = true;
		    	}
		    },
		    /*
		    updated(el, binding){
		    	el.focus();
		    }*/
		},
	},
}
</script>

<style scoped>
</style>