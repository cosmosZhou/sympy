<template>
	<textarea id='apply' name="apply">{{apply}}</textarea>
</template>

<script>
	console.log('importing new-apply.vue');
	module.exports = {
		props : [ 'apply'],
		
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

            		'Down': function(cm) {
            			var cursor = cm.getCursor();
            			if (cursor.line + 1 < cm.lineCount())
            				return cm.moveV(1, "line");

            			cm = self.$parent.$refs.prove.editor;
            			cm.focus();

            			if (cursor.ch == 0) {
            				var linesToMove = cm.getCursor().line;
            				for (let i = 0; i < linesToMove; ++i) {
            					cm.moveV(-1, "line");
            				}
            			}
            			else
            				cm.setCursor(0, cursor.ch - 4);
            		},

            		'Up': function(cm) {
            			var cursor = cm.getCursor();
            			if (cursor.line > 0)
            				return cm.moveV(-1, "line");

            			input = document.querySelector('input[name=module]');

            			input.focus();
            			if (cursor.ch != 0) {
            				input.selectioinStart = cursor.ch;
            				input.selectioinEnd = cursor.ch;
            			}

            		},
            	});
            	
            	this.editor = CodeMirror.fromTextArea(this.$el, {
    				mode: {
    					name: "python",
    					singleLineStringErrors: false
    				},

    				theme: 'eclipse',

    				//lineNumbers: true,
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