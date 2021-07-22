<template>
	<div>
		>>> <input v-focus spellcheck=false type=text v-model=script
			:size=size @keydown=keydown />
		<div if=latex v-html=latex></div>
	</div>
</template>

<script>
	console.log('importing console-statement.vue');
	module.exports = {		
		props : [ 'script', 'latex'],
		
		data(){
			return {
				copiedFrom: -1,
			};
		},
		
		computed: {
			size(){
				return Math.max(this.script.length, 32);
			},
			
			user(){
				return sympy_user();				
			},
			
			hash(){
				var hash = location.hash;
				if (hash){
					hash = hash.slice(1);					
					hash = parseInt(hash);					
					return hash;
				}
	    		return -1;
			},
		},
		
		updated() {
			MathJax.typesetPromise();
		},
		
		created(){
		},
		
		methods: {
			keydown(event){
				switch(event.key){
				case 'Enter':
					console.log("Enter is pressed");
					var inputs = this.$parent.$refs.input;
					var index = inputs.indexOf(this);
					if (window.axios){
						var value = event.target.value;
						if (index == inputs.length - 1){
							axios.post('eval', {py: value}).then(res => {
								console.log('res = ' + res.data);
								var latex = res.data;
								
								var statements = this.$parent.statements;
								lastStatement = statements.back();
								lastStatement.script = this.script;						
								this.latex = latex;
								lastStatement.latex = latex;						
								statements.push({script: '', latex: ''});
								
							}).catch(err => {
								console.log(err);
								this.latex = errDescription;
							});						
						}
						else{
							var value = [];
							for (var i = index; i < inputs.length; ++i){
								value.push(inputs[i].script);
							}
							value = value.join('\n');
							axios.post('eval', {py: value, multiple: true}).then(res => {
								console.log('res = ' + res.data);
								var latex = res.data;
								for (var i = 0; i < latex.length; ++i){
									inputs[index + i].latex = latex[i];
								}
								
							}).catch(err => {
								console.log(err);
								this.latex = errDescription;
							});					
						}
					}
					else{
						location.href = `${this.$parent.interactive_href}#${index}`;
					}
					break;
				case 'PageUp':
					console.log("PageUp is pressed");
					var inputs = this.$parent.$refs.input;
					var index = inputs.indexOf(this);
					--index;
					inputs[index].$el.querySelector('input').focus();
					break;
					
				case 'PageDown':
					console.log("PageDown is pressed");
					var inputs = this.$parent.$refs.input;
					var index = inputs.indexOf(this);
					++index;
					inputs[index].$el.querySelector('input').focus();
					break;
					
				case 'ArrowUp':
					console.log("ArrowUp is pressed");
					var statements = this.$parent.statements;
					--this.copiedFrom;
					var index = statements.length + this.copiedFrom;
					this.script = statements[index].script;
					break;
				case 'ArrowDown':
					console.log("ArrowDown is pressed");
					var statements = this.$parent.statements;
					++this.copiedFrom;
					var index = statements.length + this.copiedFrom;
					this.script = statements[index].script;
					break;
				case 'F3':					
					console.log("F3 is pressed");
					find_and_jump(event);
					break;
				}
			},
		},	
		
		directives: {
			focus: {
			    // after dom is inserted into the document
			    inserted(el, binding, vnode) {
			    	var self = vnode.context;
			    	if (self.hash >= 0){
			    		var inputs = self.$parent.$refs.input;
						if (inputs.indexOf(self) == self.hash){
							el.focus();
						}
			    	}
			    	else{
			    		el.focus();
			    	}

			    	if (window.MathJax)
			    		MathJax.typesetPromise();
			    },
			},
		},
	};
</script>

<style>
</style>