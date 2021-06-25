<template>
	<a :href=href>{{module}}</a>
</template>

<script>
	console.log('importing hierarchy-href.vue');	

	module.exports = {
		props : [ 'module' ],

		computed: {
			user(){
				return sympy_user();
			},
			
			href(){
				return '/%s/axiom.php/'.format(this.user) + this.module.replaceAll('.', '/');
			},
			
		},
		
		methods: {
		},
	};
</script>

<style>
</style>