<template>
	<div>
		>>> <input spellcheck=false type=text v-model=script :size=size
			:readonly=readonly @keydown=keydown />
		<div if=latex v-html=latex></div>
	</div>
</template>

<script>
	console.log('importing console-statement.vue');
	module.exports = {		
		props : [ 'script', 'latex'],
		
		data(){
			return {
				readonly: false,
				copiedFrom: -1,
			};
		},
		
		computed: {
			size(){
				return Math.max(this.script.length, 32);
			},
		},
		
		updated() {
			MathJax.typesetPromise();
		},
		
		created(){
            promise(()=>{
            	this.$el.firstElementChild.focus();
            });
		},
		
		methods: {
			keydown(event){
				switch(event.key){
				case 'Enter':
					console.log("Enter is pressed");
					var value = event.target.value;
					request_get('http://localhost:5000/eval', {py: value, text: true}, "jsonp").done(res => {
						console.log('res = ' + res.latex);
						this.readonly = 'readonly';
						var statements = this.$parent.statements;
						lastStatement = statements.back();
						lastStatement.script = this.script;						
						this.latex = res.latex;
						lastStatement.latex = this.latex;						
						statements.push({script: '', latex: ''});
						
					}).fail((errInfo, errType, errDescription) => {
						if (errInfo.responseText) {
							console.log('debugging info = ');
							console.log(errInfo);
							console.log(errType);
							console.log(errDescription);
						}
						this.latex = errDescription;
					});
					break;
				case 'ArrowUp':
					console.log("Enter is pressed");
					var statements = this.$parent.statements;
					--this.copiedFrom;
					var index = statements.length + this.copiedFrom;
					this.script = statements[index].script;
					break;
				case 'ArrowDown':
					console.log("Enter is pressed");
					var statements = this.$parent.statements;
					++this.copiedFrom;
					var index = statements.length + this.copiedFrom;
					this.script = statements[index].script;
					break;
				}
			},
		},		
	};
</script>

<style>
</style>