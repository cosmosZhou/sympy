<template>
	<div>
		module :
		<new-input :module=module></new-input>
		<form name=form enctype="multipart/form-data" method=post action="">
			<new-apply ref=apply :apply=apply></new-apply>
			<br>
			<new-prove ref=prove :prove=prove></new-prove>
		</form>
	</div>
</template>

<script>
	console.log('importing new-theorem.vue');
	var	newInput = httpVueLoader('static/vue/new-input.vue');
	var	newApply = httpVueLoader('static/vue/new-apply.vue');
	var	newProve = httpVueLoader('static/vue/new-prove.vue');
	
	module.exports = {
		components: {newInput, newApply, newProve },
		props : [ 'module', 'apply', 'prove'],
		
		data(){
			return {				
			};
		},
		
		
		computed: {
    		proveEditor(){
    			var prove = [];
    			prove.push(this.$refs.prove);
    			return prove;
    		},
		},
		
		methods: {
		},
	};
</script>

<style>
</style>