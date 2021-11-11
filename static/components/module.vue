<template>
	<form name=form spellcheck=false enctype="multipart/form-data" method=post @keydown=keydown_form>
		<codeMirror ref=codeMirror :text=code :name=name :theme=theme :lineNumbers=lineNumbers :styleActiveLine=styleActiveLine :focus=focus :breakpoint=breakpoint></codeMirror>
	</form>
	<div ref=div class=log>
		<p v-for="log of log">{{log}}</p>		
	</div>
	<input ref=input spellcheck=false name=py placeholder="input inline python script to execute" :size=pyScriptSize v-model=pyScript @keydown=keydown_input>
</template>

<script>
import codeMirror from "./codeMirror.vue";
console.log('importing module.vue');
export default {
	components: {codeMirror},
	
    props : [ 'code'],

    data(){
    	return {
    		theme: 'eclipse',
    		name: 'code',
    		lineNumbers: true,
    		styleActiveLine: true,
    		focus: true,
    		user: null,
    		breakpoint: [],
    		start_line: 0,
    		log: [],
    		pyScript: '',
    		history : [],    		
    		currentIndex: -1,
    	}
    },
    
    async created(){
    	this.user = await form_get('system/user');
    	for (let [line] of await form_post('mysql/select', {sql:`select line from tbl_breakpoint_py where user = '${this.user}' and module = '${this.module}'`})){
    		this.breakpoint[line] = true;	
    	}
    	console.log("this.breakpoint.length =", this.breakpoint.length);
    	
    	var codeMirror = this.$refs.codeMirror;
    	codeMirror.$nextTick(()=>{
    		codeMirror.showBreakPoint();
    		this.run();
    	});
    },
    
    updated(){
    },
    
    computed:{
    	pyScriptSize(){
    		return Math.max(this.pyScript.length, 40);	
    	},
    	
    	lines(){
    		return this.code.split('\n');	
    	},
    	
        module(){
            return document.querySelector('title').textContent;
        },
        
        hash:{
        	get(){
            	var hash = location.hash;			
        		if (hash){
        			return hash.slice(1);
        		}   		
        	},
        	
        	set(hash){
        		if (hash)
        			location.hash = '#' + hash;
        		else
        			location.hash = '';
        	},
        },
        
        stop_line(){
    		var stop = this.start_line + 1;
    		for (; stop < this.breakpoint.length; ++stop){
    			if (this.breakpoint[stop]){
    				break;
    			}
    		}
    		return stop;
        },
        
    },
    
	mounted(){
	},
    
    methods: {
    	showExecutionPoint(){
    		var codeMirror = this.$refs.codeMirror;
    		codeMirror.showExecutionPoint(this.start_line, this.stop_line);
    		this.start_line = this.stop_line;
    	},
    	
    	async run(){
    		var lines = this.lines.slice(this.start_line, this.stop_line);    		
    		
    		var res = await json_post('debug/exec', {py: lines.join('\n')});
    		this.process_log(res);
    		
    		this.showExecutionPoint();
    	},
    	
		async resume(){
    		var lines = this.lines.slice(this.start_line, this.stop_line);    		
    		
    		var res = await json_post('debug/exec', {py: lines.join('\n')});
    		this.process_log(res);
    		
    		this.showExecutionPoint();
		},
    	
		save(){
    		if (this.breakpoint.length){
    			this.hash = null;
    		}
    		else{
    			var cursor = this.$refs.codeMirror.editor.getCursor();
    			var line = cursor.line + 1;
    			var ch = cursor.ch + 1;
    			this.hash = `${line}:${ch}`;    			
    		}
    		
    		form.submit();
		},
		
		async debug(){
			console.log("debug in sympy.vue");
			var user = sympy_user();
			var [[port]] = await form_post('php/request/mysql/select', {sql: `select port from tbl_login_py where user = '${user}'`});
			port = parseInt(port);
			
			var href = location.href;
			href = href.match(/(.+)\/[^\/]+\/(?:axiom.php|run.py|php\/\w+\.php)\b/)[1];
			location.href = `${href}:${port}/debug?module=${this.module}`;
		},    	

		set_breakpoint(line){
			this.breakpoint[line] = true;
			form_post('mysql/execute', {sql: `insert into tbl_breakpoint_py values('${this.user}', '${this.module}', ${line})`}).then(res =>{
				console.log(res);
			});
		},

		clear_breakpoint(line){
			delete this.breakpoint[line];
			form_post('mysql/execute', {sql: `delete from tbl_breakpoint_py where user = '${this.user}' and module = '${this.module}' and line = ${line}`}).then(res =>{
				console.log(res);
			});
		},
		
		keydown_form(event){
			switch(event.key){
			case 'End':
				if (event.ctrlKey){
					this.$refs.input.focus();
					event.preventDefault();
				}
				break;
			}
		},
		
		process_log(res){
    		if (res.log){
    			this.log.push(...res.log.split('\n'));
    		}
    		
    		if (res.ret){
    			this.log.push(...res.ret.split('\n'));
    		}
			
    		this.$nextTick(()=>{
    			this.$refs.div.lastElementChild.scrollIntoView();	
    		});			
		},
		
		async keydown_input(event){
			switch(event.key){
			case 'Enter':
	    		var res = await json_post('debug/eval', {py: this.pyScript});
	    		this.process_log(res);
	    		
	    		if (this.pyScript != this.history.back())
	    			this.history.push(this.pyScript);
	    		this.currentIndex = this.history.length - 1;
				break;
			case 'ArrowUp':
				if (this.currentIndex > 0){
					--this.currentIndex;
					this.pyScript = this.history[this.currentIndex];
					event.preventDefault();
				}
				break;
			case 'ArrowDown':
				if (this.currentIndex + 1 < this.history.length){
					++this.currentIndex;
					this.pyScript = this.history[this.currentIndex];
					event.preventDefault();
				}
				break;
			case 'F8':
				this.resume();
			}
		},
    },
};
</script>

<style>
div.log > p {
	margin:0 auto;
}

input {
	margin-left: 1.5em;
}

div.log{
 	height: 200px;
	overflow-y: scroll; 
	margin-left: 1.5em;
}

</style>