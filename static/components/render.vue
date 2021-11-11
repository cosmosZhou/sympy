<template>
    <div v-finish>
        <form name=form spellcheck=false enctype="multipart/form-data" method=post action="">
            <renderApply v-if=applyCode ref=apply :text=applyCode></renderApply>
            <renderProve :text="given.py" :index=0></renderProve>
            <template v-if=given.latex>
                <hr>
                <h3 title='callee hierarchy'>
                    <a style='font-size: inherit' :href="'/%s/axiom.php?callee=%s'.format(user, module)">
                        <font color=blue>{{given_hint}}:</font>
                    </a>
                </h3>
                <p>{{given.latex}}</p>
            </template>

            <template v-if=where>
                <hr>
                <h3 title='caller hierarchy'>
                    <a style='font-size: inherit' :href="'/%s/axiom.php?caller=%s'.format(user, module)">
                        <font color=blue>where:</font>
                    </a>
                </h3>
                <p>{{where}}</p>
            </template>

            <hr>
            <h3 title='callee hierarchy'>
                <a style='font-size: inherit' :href="'/%s/axiom.php?callee=%s'.format(user, module)">
                    <font color=blue>{{imply_hint}}:</font>
                </a>
            </h3>
            <p>{{imply}}</p>

            <hr>
            <h3 title='caller hierarchy'>
                <a style='font-size: inherit' :href="'/%s/axiom.php?caller=%s'.format(user, module)">
                    <font color=blue>prove:</font>
                </a>
            </h3>

            <template v-for="(p, index) in prove">
                <renderProve :text="p.py" :index="index + 1"></renderProve>
                <p>{{p.latex}}</p>
            </template>

            <template v-for="(_, i) in unused.length">
                <renderProve :text="unused[i]" :index="i + prove.length + 1"></renderProve>
                <br>
            </template>

        </form>

        <template v-if="logs.length != 0">
            <br><br>
            <h3>debugging information is printed as follows:</h3>
        </template>

        <font v-for="(err, index) of error" class=error :title=err.file @click="click_font(index, err.line)">
            <template v-if=!index>
            	{{err.type}}: {{err.info}}<br>
            </template>
            {{err.code}}<br>
        </font>

        <div v-for="log in logs" v-cloak>
            <p>{{log}}</p>
        </div>
        
        <div class=bottom-right>
            <p>
                <font size=2>Created on {{createdTime}}</font>
                <br>
                <font size=2>Updated on {{updatedTime}}</font>
            </p>
        </div>
        
    </div>
</template>

<script>
console.log('importing render.vue');
var renderedAlready = false;
import renderProve from "./renderProve.vue"
import renderApply from "./renderApply.vue"

export default {
    components: {renderProve, renderApply},
    props : [ 'prove', 'logs', 'error', 'given', 'imply', 'module', 'unused', 'where', 'createdTime', 'updatedTime'],
    
    async created(){
    	if (this.hash)
        	this.applyCode = await form_post("php/request.php", { apply: this.module });
    },
    
    data(){
        return {
        	renderProve: [],
        	applyCode: '',
        };        
    },
    
    computed: {
        user(){
            return sympy_user();
        },

        numOfRequisites(){
            var m = this.module.match(/([\w.]+)\.(imply|given)\./);
            if (m.length){
                return m[1].split('.').length - 1;
            }
            return 0;
        },
        
        imply_hint(){
            if (this.module.indexOf('.given.') >= 0)
                return 'given';
            return 'imply';
        },
        
        given_hint(){
            if (this.module.indexOf('.given.') >= 0)
                return 'imply';
            return 'given';
        },
        
        module(){
        	return location.href.match(/axiom\.php\?module=([\/\w.]+)/)[1];
        },
        
        hash(){
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        }
    },

    updated(){
    },
    
    mounted(){
    },
    
    methods: {
        async open_apply(hash){
            if (this.applyCode) {
                this.$refs.apply.editor.focus();
            }
            else {
            	this.applyCode = await form_post("php/request.php", { apply: this.module });
            }                
        },
        
        click_font(index, line) {
        	console.log(`index = ${index}, line = ${line}`);
        	var error = this.error[index];
        	switch(error.func){
        	case 'prove':
                var line = this.error.line;
                var sum = 0;
                
                console.log("this.renderProve.length = " + this.renderProve.length);
                for (let cm of this.renderProve) {
                    cm = cm.editor;
                    var _sum = sum;
                    sum += cm.lineCount();
                    if (sum > line) {
                        cm.focus();
                        cm.setCursor(line - _sum, 0);
                        break;
                    }
                }
            	break;
        	case 'apply':
                console.log(error);
                var module = error.file.match(/axiom\.([\w.]+)/)[1];
                if (module == this.module) {
                	this.open_apply(error.line);
                }
                else{
                    var href = location.href;
                    href = href.match(/(.+\/axiom.php\?module=).+/)[1];                    
                    href += `${module}#${line}`;
                    window.open(href);
                }
                break;
            default:
            	var file = error.file;
            	var line = error.line;
            	var href = location.href;
                href = href.match(/(.+\/axiom.php\?).+/)[1];
                var index = file.indexOf('.');
                var key = file.slice(0, index);
                var value = file.slice(index + 1);
                href += `${key}=${value}#${error.line}`;
                window.open(href);
            }
        },
        
    },
    
    directives: {
        finish :{
            mounted(el, binding){
                var self = binding.instance;
                
                console.log('module = ' + self.module);

                form_post("php/request.php", { detect: self.module }).then(theorem => {
                    console.log('theorem = ' + theorem);
                    if (!theorem)
                        return;

                    for (let cm of self.renderProve) {
                        cm = cm.editor;
                        cm.eachLine(line => {
                            var text = line.text;
                            var selectionStart = text.indexOf(theorem);
                            if (selectionStart >= 0) {
                                console.log(text);
                                var lineNo = line.lineNo();

                                cm.setCursor(lineNo, selectionStart);
                                cm.addSelection({ line: lineNo, ch: selectionStart }, { line: lineNo, ch: selectionStart + theorem.length });
                                cm.focus();
                            }
                        });
                    }
                });                    
            },
        },
    },
};

//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-clear
//http://docs.mathjax.org/en/latest/advanced/typeset.html
//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-async
//http://docs.mathjax.org/en/latest/web/typeset.html#get-math-items
</script>

<style scoped>
.error {
    color: red;
}

.error:hover {
    cursor: pointer;
}

[v-cloak] {
    display: none !important;
}

.bottom-right{
    width: auto;
    height: 50px;
    position: relative;
}

.bottom-right p{
    position: absolute;
    bottom: 0;
    right: 0;
}

</style>