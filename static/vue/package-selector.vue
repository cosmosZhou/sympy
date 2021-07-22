<template>
	<div class=packageSelector-wrapper tabindex=1 @keydown=keydown>
		move <font color=blue>{{theorem}}</font> to :
		<p>{{path}}</p>
		<div class=packageSelector>
			<small-package v-for="package, i of packages" :package=package :tabindex="i + 1"></small-package>
		</div>		
		
		<button class=confirm type=button @click=click>confirm</button>
		<button class=cancel type=button @click=click>cancel</button>
	</div>

</template>

<script>
	console.log('importing package-selector.vue');	
	var smallPackage = httpVueLoader('static/vue/small-package.vue');

	module.exports = {
		data(){
			return {
			};
		},
		
		components : {smallPackage},
	
		props : [ 'path'],
		
		asyncComputed: {
			packages() {
		    	//console.log("folders() {");
		    	var params = {folder: this.path};
		    	var sympy = sympy_user();
		        return Vue.http.get(`/${sympy}/php/request/scandir.php`, {params: params}).then(response => response.data);
		    },
		},
		
		computed: {			
			theorem(){
				var children = this.$parent.$children;
				var index = this.$parent.focusedIndex;
				return children[index].$el.textContent.trim();
			},
		},
		
		methods: {

			click(event){
				var self = event.target;
				switch (self.className){
				case 'confirm':
					var oldFile = location.href.match(/\/axiom.php\/(.+)/)[1];
					if (!oldFile.endsWith('/')){
						oldFile += '/';
					}
					oldFile += this.theorem;
					
					var user = sympy_user();
					var params = {
						theorem: oldFile.replaceAll('/', '.'), 
						dest: this.path.replaceAll('/', '.').substring(1),
					};
					
					parent = this.$parent;
					form_post(`/${user}/php/request/move/theorem.php`, params).then(res =>{
						console.log("res = " + res);
						var focusedIndex = this.$parent.focusedIndex;
						//console.log('this.$parent.theorems = ' + this.$parent.theorems);
						this.$parent.theorems.remove(focusedIndex);
						//console.log('this.$parent.theorems = ' + this.$parent.theorems);
						this.$parent.focusedIndex = -1;						
					}).catch(fail);
					
					break;
				case 'cancel':
					break;
				}			
			},
			
			focus(package){				
				if (package != null){									
					for (let child of this.$children){
						if (child.package == package){
							child.$el.focus();
							break;
						}
					}
				}
				else{
					self = this;	
				
					setTimeout(()=>{
						for (let child of self.$children){
							child.$el.focus();
							break;
						}
						
					}, 100);				
				}
			},
			
			keydown(event) {				
				var self = event.target;
				var key = event.key;

				switch (key) {
					case 'ArrowLeft':
						break;
					case 'ArrowRight':
						break;
					case 'ArrowDown':
						break;
					case 'ArrowUp':
						break;	
					case 'Home':
						break;						
					case 'End':
						break;
					case 'Backspace':
						console.log("case 'Backspace': in package-selector.vue");
						this.path = this.path.match(/(.*)\.\w+/)[1];
						
						this.focus();
						break;
					default:
						if (key.length == 1) {
						}
						break;
				}				
			},
			
		}
	};
</script>

<style>

div>div.packageSelector{
	background-color: rgb(199, 237, 204);
	position: absolute; 
	border: 1px solid #555; 
	width: 600px; 
	height: 400px;
	z-index: 10;
	padding: 7px 1px 7px 7px;
	overflow:auto;  
//	overflow-x:hidden;
//	overflow-y:hidden;
}

div button{
	position: relative; 
	bottom: 7px;
	z-index: 11;
}

div button.confirm{
	left: 220px; 
	top: 420px;
}

div button.cancel{
	left: 260px; 
	top: 420px;
}

div.packageSelector-wrapper{
	position: absolute;
	left: 436px;
	top: 207px; 
}

div.packageSelector-wrapper:focus {
	outline: none;
}

</style>