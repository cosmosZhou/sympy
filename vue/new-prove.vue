<template>
	<textarea id='prove' name="prove">{{prove}}</textarea>
</template>

<script>
	console.log('importing new-prove.vue');
	module.exports = {
		props : [ 'prove'],
		
		created(){
            promise(()=>{    
            	var self = this;
            	var value = this.$el.value;
            	
            	_extraKeys = extraKeys();
            	Object.assign(_extraKeys, {
            		'Ctrl-S': function(cm) {
            			console.log("'Ctrl-S' is pressed!");
            			var module = $('input').val();
            			console.log("module = " + module);
            			module = module.replace(/\./g, '/');
            			console.log("module = " + module);

            			form.action = "/sympy/axiom.php/" + module;
            			console.log("form.action = " + form.action);

            			console.log("save the content now");
            			form.submit();
            		},

            		'Up': function(cm) {
            			var cursor = cm.getCursor();
            			if (cursor.line > 0)
            				return cm.moveV(-1, "line");

            			cm = self.$parent.$refs.apply.editor;

            			cm.focus();
            			if (cursor.ch == 0) {
            				var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
            				for (let i = 0; i < linesToMove; ++i) {
            					cm.moveV(1, "line");
            				}
            			} else
            				cm.setCursor(cm.lineCount() - 1, cursor.ch + 4);
            		},

            	});

            	
            	this.editor = CodeMirror.fromTextArea(this.$el, {
            		mode: {
            			name: "python",
            			singleLineStringErrors: false
            		},

            		theme: 'function',
            		indentUnit: 4,
            		matchBrackets: true,

            		scrollbarStyle: null,

            		extraKeys: _extraKeys,

            		hintOptions: { hint: hint },

            	});
            });
		},
		
		updated(){
		},
		
		data(){
			return {
				editor: null,
			};
		},
		
		methods: {
		},
	};
</script>

<style>
</style>