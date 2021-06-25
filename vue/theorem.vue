<template>
	<icon class=theorem :text=theorem :lines=5></icon>
</template>

<script>
	console.log('importing theorem.vue');
	var icon = httpVueLoader('/sympy/vue/icon.vue');
	module.exports = {
		components: {icon},
		
		props : [ 'theorem'],
		
		methods: {
			dblclick(event) {
				var self = event.target;
				var text = self.textContent;
				text = text.trim();
				var href = location.href;
				if (!href.endsWith('/'))
					text = '/' + text;
				location.href += text;
			},			

			remove(){
				console.log("this.theorem = " + this.theorem);
				var href = location.href;
				var m = href.match(/\/([^\/]+)\/axiom\.php\/(.+)/);
				var user = m[1];
				var package = m[2];
				if (package.endsWith('/')){
					package = package.slice(0, -1);
				}
				
				var py = `${user}/axiom/${package}/${this.theorem}.py`;
				console.log(py);
				
				request_post(`/${user}/php/request/delete/theorem.php`, {package: package.replaceAll('/', '.'), theorem: this.theorem}).done(res => {
					console.log('res = ' + res);
				}).fail(fail);
			},
		}		
	}
</script>

<style>
.theorem {
	width: 3.2em;
	height: 5em;
	border-top: 0.4em solid #003;
	border-bottom: 0.4em solid #003;
	border-left: 0.4em solid #003;
	margin: 50px auto;
	position: relative;
}

div .theorem {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 3em;
}

.theorem:before {
	border-right: 0.4em solid #001;
	border-bottom: 0.4em solid #001;
	width: 1em;
	height: 4em;
	position: absolute;
	right: -1.3em;
	bottom: -0.4em;
	content: "";
	background: rgb(220, 220, 0);
}

.theorem:after {
	position: absolute;
	top: -0.4em;
	right: -1.3em;
	content: "";
	border-bottom: 1.4em solid #003;
	border-right: 1.4em solid transparent;
	width: 0;
	height: 0;
}
</style>