<template>
	<li :style=li_style>
   		<hierarchy-href :module=module></hierarchy-href>
   		<template v-if=modules>        			
   			<button class=transparent @click=click>{{buttonText}}</button>
   		 	<ul v-if=show>
   	 			<hierarchy-module ref=module v-for="module of modules" :module=module></hierarchy-module>
   			</ul>
		</template>				
    </li>
</template>

<script>
	console.log('importing hierarchy-module.vue');
	
	var	hierarchyHref = httpVueLoader('/sympy/vue/hierarchy-href.vue');
	
	module.exports = {
		name: 'hierarchy-module',
		
		components : {hierarchyHref},
		
		props : {
			module: null,
			show:{
				default: false,
			}
		},
		
		data(){
			return {
				backgroundColor: 'inherit',
			};
		},

		created(){
			var root = this.$root;
			if (root.deep){
				this.show = true;
			}
			else if (root.traceback){
				if (this.module == root.traceback.back()){
					this.show = false;
					this.backgroundColor = 'yellow';
				}
				else {
					if (this.module == root.traceback[this.depth]){
						this.show = true;
					}
				}
			}			
		},
		
		computed: {
			li_style(){
				return `background-color:${this.backgroundColor}`;	
			},
			
			depth(){
				var depth = -1;
				var root = this.$root;
				var parent = this.$parent;
				for (;;){
					if (parent === root)
						break;

					++depth;
					parent = parent.$parent;
				}
				
				return depth;
			},
			
			buttonText(){
				return this.show? '<<<<' : '>>>>';
			},
			
			modules(){
				return this.$root.graph[this.module];
			},
		},
		
		methods: {
			click(event) {
				this.show = !this.show;
			},	
			
		},
	};
</script>

<style scoped>

button.transparent:hover{
	background-color: red;
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

ul li {
	margin-top: 0.5em;
}

</style>