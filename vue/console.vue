<template>
	<div>
		interactive python console: 			
		<label>
			<input type=checkbox v-model=checked @change=change>
			Display style
		</label>
		<br>
		<console-statement v-for="statement of statements" :script=statement.script :latex=statement.latex>
		</console-statement>
	</div>
</template>

<script>
	console.log('importing console.vue');
	var	consoleStatement = httpVueLoader('/sympy/vue/console-statement.vue');
	
	module.exports = {
		components: {consoleStatement },
		props : [ 'statements'],
		
		data(){
			return {
				checked: true,
			};
		},
		
		methods: {
			change(event){
				var length = this.statements.length;
				for (let i = 0; i < length; ++i){					
					var latex = this.statements[i].latex;
					if (latex.startsWith('$$')){
						latex = latex.slice(1, -1);
					}
					else{
						if (latex)
							latex = `$${latex}$`;
					}
					this.statements[i].latex = latex;
					this.$children[i].latex = latex;
				}
			},
		},
	};
</script>

<style>
</style>