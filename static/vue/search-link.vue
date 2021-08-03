<template>
	<input v-if="mode != 'a'" v-focus spellcheck=false 
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
				mode: 'a',
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
			
			mode(newValue, oldValue){
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
				if (this.mode == 'F3'){
					this.mode = 'input';
				}
				else{
					this.module = event.target.value;
					this.mode = 'a';	
				}				
			},
			
			keydown(event){
				switch(event.key){
				case 'Enter':
					this.module = event.target.value;
					this.mode = 'a';					
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