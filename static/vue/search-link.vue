<template>
	<input v-if="is_edit" v-focus spellcheck=false 
		:size='module.length + 1' :value=module 
		@blur=blur @keydown=keydown />
	<a v-else v-focus tabindex=2 :href=href 
		@contextmenu.prevent=contextmenu @keydown=keydown_a>
       	{{module}}
       	<search-contextmenu v-if='showContextmenu' :left=left :top=top></search-contextmenu>
    </a>
</template>

<script>
	console.log('importing search-link.vue');
	var searchContextmenu = httpVueLoader('static/vue/search-contextmenu.vue');	
	var focusedAlready = false;
	
	module.exports = {
		components: {searchContextmenu},
		
		data(){
			return {
				is_edit: false,
				showContextmenu: false,
				left: -1,
				top: -1,
			};
		},
		
		props: [
			'module',
		],
		
		watch:{
			module(newText, oldText){
				if (oldText == newText){
					return;	
				}
			
				console.log('oldText = ' + oldText);
				console.log('newText = ' + newText);			
				
				var sympy = sympy_user();
				
				var self = this.$parent;
				form_post(`php/request/rename.php`, { old: oldText, new: newText}).then(res => {
					console.log('res = ' + res);					
				}).catch(fail);
			},
			
			is_edit(newValue, oldValue){
				if (oldValue == newValue){
					return;
				}
				focusedAlready = false;
			},
			
		},
		
		computed: {
			user(){
				return sympy_user();
			},
			
			href(){
				return `/${this.user}/axiom.php?module=${this.module}`;
			},			
		},
		
		methods: {			
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
				this.module = event.target.value;
				this.is_edit = false;
			},
			
			keydown(event){
				switch(event.key){
				case 'Enter':
					this.module = event.target.value;
					this.is_edit = false;					
					break;
				}
			},
			
			keydown_a(event){
				switch(event.key){
				case 'F2':
					this.is_edit = true;
					break;
				}				
			},
		},
		
		directives: {
			focus: {
			    // after dom is inserted into the document
			    inserted(el, binding, vnode) {
			    	if (!focusedAlready){
			    		el.focus();
			    		focusedAlready = true;
			    	}			    		
			    },
			},
		},	
		
	};
</script>

<style scoped>
</style>