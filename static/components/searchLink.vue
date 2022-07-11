<template>
	
	<a v-if="mode == 'a'" v-focus tabindex=2 :href=href @contextmenu.prevent=contextmenu @keydown=keydown_a>
       	{{module}}
       	<searchContextmenu v-if='showContextmenu' :left=left :top=top></searchContextmenu>
    </a>
	<span v-else-if="mode == 'span'">
       	{{module}}
    </span>
    <input v-else v-focus spellcheck=false :size='module.length + 1' :value=module @blur=blur @keydown=keydown>
    
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
		async delete_folder(error_msg){
			while (error_msg){
				console.log('error_msg = ', error_msg);				
				var m = error_msg.matchAll(/rmdir\((\S+)\)/g);
				error_msg = '';
				for (var m of m){
					var folder = m[1];
					var names = folder.split(/[\/\\]/);
					var index = names.indexOf('axiom');
					names = names.slice(index + 1);
					var section = names.pop();
					var parentFolder = names.join('.');
					//error_msg += await form_post(`php/request/delete/package.php`, { package: parentFolder, section});
				}
			}
		},
		
		async set_module(module){
			var undeletables = '';
			if (this.module != module){
				console.log('oldText = ' + this.module);
				console.log('newText = ' + module);			
				
				undeletables = await form_post(`php/request/rename.php`, { old: this.module.replace(/\//g, '.'), new: module.replace(/\//g, '.')});
				console.log('undeletables = ' + undeletables);
				
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
			}

			this.mode = 'a';
			return undeletables;
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
				this.mode = 'span';
				focusedAlready = false;
				this.$nextTick(async ()=>{
					var undeletables = await this.set_module(event.target.value);
					console.log("undeletable files = ", undeletables);
					
					this.delete_folder(undeletables);
				});
			}				
		},
		
		async keydown(event){
			switch(event.key){
			case 'Enter':
				var undeletables = await this.set_module(event.target.value);
				console.log("undeletable files = ", undeletables);
				this.delete_folder(undeletables);
				
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

		    updated(el, binding){
		    	el.focus();
		    }
		},
	},
}
</script>

<style scoped>
</style>