<template>
    <textarea name="prove[]" v-focus>{{prove}}</textarea>
</template>

<script>
console.log('importing renderProve.vue');
export default {
    props : [ 'prove', 'index'],
    
    created(){
        this.$parent.renderProve[this.index] = this;
    },
    
    updated(){
    },
    
    computed:{
        firstSibling(){
            var prove = this.$parent.renderProve;
            return prove[0];                
        },
        
        nextSibling(){
            var prove = this.$parent.renderProve;
            var i = prove.indexOf(this);
            return prove[i + 1];                
        },

        previousSibling(){
            var prove = this.$parent.renderProve;
            var i = prove.indexOf(this);
            return prove[i - 1];                
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
            mounted(el, binding) {
                var self = binding.instance;
                var _extraKeys = extraKeys();
                
                if (self.$parent.renderProve instanceof Array){
                    var i = self.$parent.renderProve.indexOf(self);    
                }
                else{
                    var i = 0;
                }
                
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
                        
                        location.hash = search.substring(index);
                        location.search = search.substring(0, index);
                    },
                    
                    Left(cm) {
                        cm.moveH(-1, "char");
                        if (cm.getCursor().hitSide) {
                            if (i == 0) {
                                cm = self.$parent.$refs.apply;
                            }
                            else {
                                cm = proveEditors[i - 1];
                            }
                            cm = cm.editor;
                            
                            cm.focus();
                            CodeMirror.commands.goDocEnd(cm);
                        }
                    },

                    Right(cm) {
                        cm.moveH(1, "char");
                        if (cm.getCursor().hitSide) {
                            cm = proveEditors[i + 1];
                            cm.focus();
                            CodeMirror.commands.goDocStart(cm);
                        }
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

                    PageDown(cm) {
                        var cursor = cm.getCursor();
                        if (cursor.line + 18 < cm.lineCount())
                            return cm.moveV(1, "page");

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

                    Up(cm) {
                        var cursor = cm.getCursor();
                        if (cursor.line > 0)
                            return cm.moveV(-1, "line");
                        if (i == 0) {
                            cm = self.$parent.$refs.apply;
                        }
                        else {
                            cm = self.previousSibling;
                        }
                        cm = cm.editor;
                        
                        cm.focus();
                        if (cursor.ch == 0 || i == 0) {
                            var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
                            for (let i = 0; i < linesToMove; ++i) {
                                cm.moveV(1, "line");
                            }
                        } else
                            cm.setCursor(cm.lineCount() - 1, cursor.ch);
                    },

                    "Ctrl-Enter": cm => {
                        CodeMirror.commands.newlineAndIndent(cm);            
                    },
                    
                    PageUp(cm) {
                        var cursor = cm.getCursor();
                        if (cursor.line >= 18)
                            return cm.moveV(-1, "page");
                        if (i == 0) {
                            cm = self.$parent.$refs.apply;
                        }
                        else {
                            cm = self.previousSibling;
                        }

                        cm = cm.editor;
                        cm.focus();
                        if (cursor.ch == 0 || i == 0) {
                            var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
                            for (let i = 0; i < linesToMove; ++i) {
                                cm.moveV(1, "line");
                            }
                        }
                        else
                            cm.setCursor(cm.lineCount() - 1, cursor.ch);
                    },

                    F3(cm){
                    	F3(cm, false, self.$parent);
                    },

                    'Ctrl-F3': cm => F3(cm, true, self.$parent),

                    'Ctrl-End': cm => {
                        cm = self.$parent.renderProve.back().editor;
                        cm.focus();
                        return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
                    },

                    'Ctrl-Home': cm => {
                        cm = self.$parent.$refs.apply;
                        if (cm == null) {
                            cm = self.firstSibling;
                        }
                        cm = cm.editor;
                        cm.focus();
                        return cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
                    },       
                    
                    /*'Shift-Down': cm => {
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
                    },*/
                    
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
                        hint(cm, options){
                            options.context = self;
                            return hint(cm, options);
                        },  
                    },

                    //equivalently:        
                    //CodeMirror.registerHelper("hint", "python", hint);
                });
                    
                if (!i && !self.$parent.apply)
                    self.editor.focus();                    
            },
        },
    },
};
</script>

<style>
</style>