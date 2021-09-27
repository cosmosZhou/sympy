<template>
	<div>
		module :
		<new-input :module=module></new-input>
		<form name=form enctype="multipart/form-data" method=post action="">
			<newApply ref=apply :apply=apply></newApply>
			<br>
			<newProve ref=prove :prove=prove></newProve>
		</form>
	</div>
</template>

<script>
console.log('importing newTheorem.vue');
import newInput from "./newInput.vue"
import newApply from "./newApply.vue"
import newProve from "./newProve.vue"

export default {
	components: {newInput, newApply, newProve },
	props : [ 'module', 'apply', 'prove'],
	
	data(){
		return {
		};
	},
	
	computed: {
		renderProve(){
   			var prove = [];
   			prove.push(this.$refs.prove);
   			return prove;
   		},
	},
	
	methods: {
	},
}
</script>

<style>
</style>