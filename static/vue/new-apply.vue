<template>
	<textarea v-focus name=apply>{{apply}}</textarea>
</template>

<script>
	console.log('importing new-apply.vue');
	module.exports = {
		props : [ 'apply'],
		
		created(){
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
		
		directives: {
			focus: {
			    // after dom is inserted into the document
			    inserted(el, binding, vnode) {
					var self = vnode.context;
	            	
	            	var _extraKeys = extraKeys();
	            	Object.assign(_extraKeys, {
	            		'Ctrl-S': function(cm) {
	            			saveDocument();
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
	            	
	            	self.editor = CodeMirror.fromTextArea(el, {
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
			    },
			},
		},
				
	};
</script>

<style>
</style>