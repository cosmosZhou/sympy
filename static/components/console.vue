<template>
	<div>
		<template v-if=readonly>
			this document is readonly, trying to edit it will cause the page to jump to 
			<a :href=interactive_href>interactive python console</a>
		</template>
		
		<template v-else>
			interactive python console
		</template>		
		: 			
		<label>
			<input type=checkbox v-model=checked @change=change>
			Display style
		</label>
		<br>
		<consoleStatement ref=input v-for="statement of statements" :script=statement.script :latex=statement.latex>
		</consoleStatement>
	</div>
</template>

<script>
console.log('importing console.vue');
import consoleStatement from "./consoleStatement.vue"
export default {
	components: {consoleStatement },
	props : [ 'statements'],
	
	data(){
		return {
			checked: true,
		};
	},
	
	computed: {
		interactive_href(){
			var port = 5000;
			var symbol = location.search.match(/\?symbol=(\w+)/)[1];
			return `${location.origin}:${port}/${symbol}`;				
		},
		
		readonly(){
			return location.search;
		},
	},
	
	methods: {
		change(event){
			var length = this.statements.length;
			for (let i = 0; i < length; ++i){					
				var latex = this.statements[i].latex;
				if (latex.startsWith('\\[')){
					//latex = latex.slice(1, -1);
					latex = latex.slice(2, -2);
					latex = `\\(${latex}\\)`;
				}
				else{
					if (latex){
						latex = latex.slice(2, -2);
						latex = `\\[${latex}\\]`;
					}							
				}
				
				this.statements[i].latex = latex;
				this.children[i].latex = latex;
			}
		},
	},
	
	mounted(){
		//document.querySelector('input:last-child').focus();
	},
}
</script>

<style>
</style>