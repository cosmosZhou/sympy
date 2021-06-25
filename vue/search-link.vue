<template>
	<input spellcheck=false v-if="is_edit" 
		:size='module.length + 1' :value=module 
		@blur=blur @keydown=keydown />
	<a tabindex=2 v-else :href=href 
		@contextmenu.prevent=contextmenu @keydown=keydown_a>
       	{{module}}
       	<search-contextmenu v-if='showContextmenu' :left=left :top=top></search-contextmenu>
    </a>
</template>

<script>
	console.log('importing search-link.vue');
	var searchContextmenu = httpVueLoader('/sympy/vue/search-contextmenu.vue');
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
				request_post(`/${sympy}/php/request/rename.php`, { old: oldText, new: newText}).done(res => {
					console.log('res = ' + res);					
				}).fail(fail);
			},
		},
		
		computed: {
			user(){
				return sympy_user();
			},
			
			href(){
				var module = this.module.replace(/\./g, '/');
				return `/${this.user}/axiom.php/${module}`;
			},
		},
		
		methods: {
			contextmenu(event) {
				//console.log("contextmenu: function(event)");
				var self = event.target;				
				
				this.left = event.x;
				this.top = event.y;				
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
					
					self = this;
					setTimeout(()=>{
						self.$el.focus();				
					}, 100);
					
					break;
				}
			},
			
			keydown_a(event){
				switch(event.key){
				case 'F2':
					this.is_edit = true;
					self = this;
					setTimeout(()=>{
						self.$el.focus();				
					}, 100);				
					
					break;
				}				
			},
		},
	};
</script>

<style scoped>
</style>