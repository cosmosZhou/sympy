<template>
	<icon class=package :text=package :lines=3></icon>
</template>

<script>
	console.log('importing package.vue');
	var icon = httpVueLoader('static/vue/icon.vue');
	module.exports = {
		components: {icon},

		props : ['package'],

		methods : {
			dblclick(event) {
				var self = event.target;
				var text = self.textContent;
				text = text.trim(); 
				var search = location.search;
				if (search.indexOf('.') >= 0){
					if (search.endsWith('.'))
						search += text + '.';
					else
						search += '.' + text + '.';
				}
				else{
					if (search.endsWith('/'))
						search += text + '/';
					else
						search += '/' + text + '/';
				}

				location.search = search;
			},
			
			remove(){
				console.log("this.package = " + this.package);
				var href = location.href;
				var m = href.match(/\/([^\/]+)\/axiom\.php\?module(.+)/);
				var user = m[1];
				var section = m[2];
				if (section.endsWith('.')){
					section = section.slice(0, -1);
				}
				
				form_post(`php/request/delete/package.php`, {section: section, package: this.package}).then(res => {
					console.log('res = ' + res);
				}).catch(fail);

			},
		}
	}
</script>

<style>

.package {
	width: 5em;
	height: 3em;
	margin: 50px auto;
	position: relative;
	height: 3em;
	z-index: 1;
}

div .package {
	display: inline-block;
	background: rgb(220, 220, 0);
	text-align: center;
	margin-right: 1.6em;
	background: rgb(220, 220, 0);
	border-top-left-radius: 0.3em;
	border-top-right-radius: 0.3em;
}

.package:before {
	width: 3em;
	height: 1em;
	position: absolute;
	left: 0.3em;
	top: -0.7em;
	content: "";
	background: rgb(220, 180, 0);
	border-top-left-radius: 0.3em;
	border-top-right-radius: 0.3em;
	box-shadow: 0.2em 0.2em 0 0 #9da0a0;
	z-index: 0;
}

.package:after {
	position: absolute;
	content: "";
}

</style>