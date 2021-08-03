<template>
	<textarea name="apply" v-focus>{{apply}}</textarea>
</template>

<script>
	console.log('importing render-apply.vue');
	module.exports = {
		props : [ 'apply', 'applyArg'],
		
		created(){
		},
		
		updated(){
		},
		
		computed: {
			nextSibling(){
				var prove = this.$parent.proveEditor;
				return prove[0];				
			},
			
			lastSibling(){
				var prove = this.$parent.proveEditor;
				return prove[prove.length - 1];				
			},
			
			user(){
				return sympy_user();
			},
			
			module(){
				return document.querySelector('title').textContent;
			},
			
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
	            		'Ctrl-O': function(cm) {
	            			console.log("'Ctrl-O' is pressed!");
	            			var href = `/${self.user}/axiom.php?new=${self.module}`;
	            			window.open(href);
	            		},

	            		'Ctrl-S': function(cm) {
	            			console.log("'Ctrl-S' is pressed!");
	            		},

	            		'Ctrl-F11': function(cm) {
	            			form.submit();
	            		},

	            		'Shift-Alt-W': function(cm) {
	            			console.log('Shift-Alt-W');
	            			var search = location.search;
	            			var index = search.lastIndexOf('.') + 1;
	            			if (!index)
	            				index = search.lastIndexOf('/') + 1;
	            			
	            			location.search = search.substring(0, index);
	            		},
	            		
	            		"Ctrl-Enter": cm => {
	            			CodeMirror.commands.newlineAndIndent(cm);			
	            		},
	            		
	    				Down(cm) {
	    					var cursor = cm.getCursor();
	    					if (cursor.line + 1 < cm.lineCount())
	    						return cm.moveV(1, "line");

	    					cm = self.nextSibling.editor;
	    					cm.focus();
	    					if (cursor.ch == 0) {
	    						var linesToMove = cm.getCursor().line;
	    						for (let i = 0; i < linesToMove; ++i) {
	    							cm.moveV(-1, "line");
	    						}
	    					}
	    					else
	    						cm.setCursor(0, cursor.ch);
	    				},

	    				Right(cm) {
	    					cm.moveH(1, "char");
	    					if (cm.getCursor().hitSide) {
	    						cm = proveEditors[0];
	    						cm.focus();
	    						CodeMirror.commands.goDocStart(cm);
	    					}
	    				},

	    				PageDown(cm) {
	    					var cursor = cm.getCursor();
	    					if (cursor.line + 18 < cm.lineCount())
	    						return cm.moveV(1, "page");

	    					cm = proveEditors[0];
	    					cm.focus();
	    					if (cursor.ch == 0) {
	    						var linesToMove = cm.getCursor().line;
	    						for (let i = 0; i < linesToMove; ++i) {
	    							cm.moveV(-1, "line");
	    						}
	    					} else
	    						cm.setCursor(0, cursor.ch);
	    				},

	    				F3,

	    				'Ctrl-F3': cm => F3(cm, true),

	    				'Ctrl-End': cm => {
	    					cm = self.lastSibling.editor;
	    					cm.focus();
	    					return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
	    				},

	            		'Ctrl-Home': cm => {
	            			cm = self.editor;
	            			return cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
	            		},            		
	            	});
	            	
	            	self.editor = CodeMirror.fromTextArea(el, {
	            		mode: {
	            			name: "python",
	            			singleLineStringErrors: false
	            		},

	            		theme: 'eclipse',

	            		indentUnit: 4,

	            		matchBrackets: true,

	            		scrollbarStyle: null,

	            		extraKeys: _extraKeys,

	            		hintOptions: { hint: hint }
	            	});
	            	
	            	self.editor.focus();
	            	
	            	if (self.applyArg == null){
	            		return;
	            	}
	            	
       				if (typeof self.applyArg == 'number' || self.applyArg.match(/^\d+/)) {
       					self.editor.setCursor(parseInt(self.applyArg), 4);
       					return;
       				}
       				
  					var regex = eval(`/((?:    )*def ${self.applyArg})\\([^()]+\\):\\s*$/`);

  					var size = self.editor.lineCount();
  					for (var index = 0; index < size; ++index) {
  						var line = self.editor.getLine(index);
  						//console.log(line);

  						var m = line.match(regex);
  						if (m) {
  							self.editor.setCursor(index, m[1].length - self.applyArg.length / 2);
  							break;
  						}
  					}
			    },			    
			},
		},
		
	};
</script>

<style>
</style>