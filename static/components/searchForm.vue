<template>
	<form name=search enctype="multipart/form-data" method=post :action=action @keydown=keydown>
		<input v-focus tabindex=1 type=text spellcheck=false name=keyword size=48 v-model=keyword placeholder='input a hint for search of a theorem/axiom'>
		<br>
			 
		<input tabindex=-1 type=checkbox name=caseSensitive v-model=caseSensitive><u>C</u>ase 
			
		<input tabindex=-1 type=checkbox name=wholeWord v-model=wholeWord><u>W</u>holeWord 
		
		<input tabindex=-1 type=checkbox name=regularExpression v-model=regularExpression>Rege<u>x</u>
		
		<input tabindex=-1 type=checkbox name=nlp v-model=nlp><u>N</u>lp
	</form>
</template>

<script>
console.log('importing searchForm.vue');
export default {
	props : ['keyword', 'caseSensitive', 'wholeWord', 'regularExpression', 'nlp'],

	computed: {
		user(){
			return sympy_user();	
		}, 
		
		action(){
			return `/${this.user}/axiom.php`;
		},
	},
	
	methods: {
		keydown(event){
			if (event.altKey){
				switch(event.key){
				case 'c':
					setAttribute(this, 'caseSensitive', !this.caseSensitive);
					break;
				case 'w':
					setAttribute(this, 'wholeWord', !this.wholeWord);
					break;
				case 'x':
					setAttribute(this, 'regularExpression', !this.regularExpression);
					break;
				case 'n':
					setAttribute(this, 'nlp', !this.nlp);
					break;
				}
			}
		},
	},	
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
				el.focus();
		    },
		},
	},
};
</script>

<style scoped>
form[name=search] {
	float: right;
}
</style>