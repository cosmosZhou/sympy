<template>
	<textarea v-focus name=prove>{{prove}}</textarea>
</template>

<script>
	console.log('importing new-prove.vue');
	module.exports = {
		props : [ 'prove'],
		
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

	            	
	            	self.editor = CodeMirror.fromTextArea(el, {
	            		mode: {
	            			name: "python",
	            			singleLineStringErrors: false
	            		},

	            		theme: 'function',
	            		indentUnit: 4,
	            		matchBrackets: true,

	            		scrollbarStyle: null,

	            		extraKeys: _extraKeys,

	            		hintOptions: { 
	            			hint(cm, options) {
	            				options.context = self;
	            				return hint(cm, options);	
	            			}, 
	            		},
	            	});
			    },
			},
		},
		
	};
</script>

<style>
</style>