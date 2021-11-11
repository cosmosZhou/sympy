<template>
	<div>
		the axiom in question is a 
		<a :href="'axiom.php?' + keyInput + '=' + this.$parent.module + (deep ? '#deep': '')" :title="'show ' + (deep?'deep':'only first-layer') + ' hierarchy'">{{keyInput}}</a>
		in the following hierarchy, would you switch to 
		<a :href=href>{{key}}</a> hierarchy?	
	</div>
</template>

<script>
	console.log('importing hierarchyInformation.vue');	

	export default {
		props : [ 'keyInput', 'deep' ],
		computed:{	
			key(){
				return this.keyInput == 'callee'? 'caller': 'callee';
			},
			
			href(){ 
				return 'axiom.php?' + this.key + '=' + this.$parent.module;
			},
		},
		
		methods: {
		},
	};
</script>

<style>
</style>