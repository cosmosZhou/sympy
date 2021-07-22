<template>
	<div>
		<form name=form spellcheck=false enctype="multipart/form-data"
			method=post action="">
			<render-apply v-if=apply ref=apply :apply=apply :apply-arg=applyArg></render-apply>
			<render-prove ref=given :prove="given.py"></render-prove>
			<template v-if=given.latex>
				<hr>
				<h3 title='callee hierarchy'>
					<a style='font-size: inherit'
						:href="'/%s/axiom.php?callee=%s'.format(user, module)"><font
						color=blue>{{given_hint}}:</font></a>
				</h3>
				<p>{{given.latex}}</p>
			</template>

			<template v-if=where>
				<hr>
				<h3 title='caller hierarchy'>
					<a style='font-size: inherit'
						:href="'/%s/axiom.php?caller=%s'.format(user, module)"><font
						color=blue>where:</font></a>
				</h3>
				<p>{{where}}</p>
			</template>

			<hr>
			<h3 title='callee hierarchy'>
				<a style='font-size: inherit'
					:href="'/%s/axiom.php?callee=%s'.format(user, module)"><font
					color=blue>{{imply_hint}}:</font></a>
			</h3>
			<p>{{imply}}</p>

			<hr>
			<h3 title='caller hierarchy'>
				<a style='font-size: inherit'
					:href="'/%s/axiom.php?caller=%s'.format(user, module)"><font
					color=blue>prove:</font></a>
			</h3>

			<template v-for="(p, i) in prove">
				<render-prove ref=prove :prove="p.py"></render-prove>
				<p>{{p.latex}}</p>
			</template>

			<template v-for="(_, i) in unused.length">
				<render-prove ref=prove :prove="unused[i]"></render-prove>
				<br>
			</template>

		</form>

		<template v-if="logs.length != 0">
			<br> <br>
			<h3>debugging information is printed as follows:</h3>
		</template>

		<div v-for="log in logs" v-cloak>
			<p v-if="typeof log == 'string'">{{log}}</p>
			<font v-else class=error :title=log.module @click=click>
				{{log.code}}<br> {{log.type}}: {{log.error}}<br>
			</font>
		</div>

	</div>
</template>

<script>
	console.log('importing render.vue');
	var renderedAlready = false;
	var	renderProve = httpVueLoader('static/vue/render-prove.vue');
	var	renderApply = httpVueLoader('static/vue/render-apply.vue');
	
	module.exports = {
		components: {renderProve, renderApply },
		props : [ 'prove', 'logs', 'given', 'imply', 'module', 'apply', 'applyArg', 'unused', 'where'],
		
		created(){
		},
		
		data(){
			return {				
			};		
		},
		
    	computed: {
    		user(){
    			return sympy_user();
    		},

    		error() {
    			for (let log of this.logs) {
    				if (typeof log == 'string')
    					continue;
    				return log;
    			}
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
    		
    		proveEditor(){
    			var prove = [];
    			prove.push(this.$refs.given);
    			return prove.concat(this.$refs.prove);
    		},
    	},

		updated(){
//    		if (window.MathJax)
//    			MathJax.typesetPromise();	
    	},
    	
		mounted(){
//    		if (window.MathJax)
//    			MathJax.typesetPromise();	
    	},
    	
		methods: {
			open_apply(arg){
		    	if (this.apply) {
		    		this.$refs.apply.editor.focus();
		    	}
		    	else {
		    		var module = location.href.match(/axiom\.php\?module=([\/\w.]+)/)[1];

		    		form_post("php/request.php", { apply: module }).then(code => {
		    			console.log('code = ' + code);
		    			this.apply = code;
		    			this.applyArg = arg;
		    		}).catch(fail);
		    	}				
			},
			
    		click(event) {
    			if (this.error.prove) {
    				var line = this.error.line;
    				var sum = 0;
    				
    				console.log("this.proveEditor.length = " + this.proveEditor.length);
    				for (let cm of this.proveEditor) {
    					cm = cm.editor;
    					var _sum = sum;
    					sum += cm.lineCount();
    					if (sum > line) {
    						cm.focus();
    						cm.setCursor(line - _sum, 0);
    						break;
    					}
    				}
    			}
    			else if (this.error.apply) {
    				console.log(this.error);
    				var line = this.error.line;

    				if (this.error.module) {
    					var href = location.href;
    					href = href.match(/(.+\/axiom.php\?module=).+/)[1];
    					href += this.error.module;
    					href += `&apply=${line}`;
    					window.open(href);
    				}
    				else{
    					this.open_apply(line);
    				}
    			}
    		},
			
		},
		
/*		directives: {
			render: {
			    // after dom is inserted into the document
			    inserted(el, binding, vnode) {
			    	let options = MathJax.getMetricsFor(el);			    	
					options.display = true;					
					options.format = 'TeX';
					
					console.log('render');
					console.log(el);
					var tex = [];
					
					for (let m of el.textContent.matchAll(/\\\[(.+?)\\\]/g)){
						tex.push(m[1]);
					}
					
					el.innerHTML = '';
					//el.firstChild.remove();
					
					for (let t of tex){
						MathJax.texReset();
						MathJax.tex2chtmlPromise(t, options).then((el => html => {
							el.appendChild(html);
							MathJax.startup.document.updateDocument();
						})(el));
					}
			    },
			},
			
			finish :{
				bind(el, binding, vnode){
					console.log('before rendering');
					MathJax.texReset();					
				},
				
				componentUpdated(el, binding, vnode){
					console.log('finish rendering');
					console.log(el);
	    	        MathJax.startup.document.clear();
	    	        MathJax.startup.document.updateDocument();
				},
			},
		},*/
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
</style>