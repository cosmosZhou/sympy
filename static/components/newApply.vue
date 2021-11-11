<template>
	<textarea name=apply>{{text}}</textarea>
</template>

<script>
console.log('importing newApply.vue');
import codeMirror from "./codeMirror.vue";

export default {
	props : [ 'text'],
	
	computed:{
		previousSibling(){
        	return this.$parent.newInput;
        },
        
        firstSibling(){
            return this.$parent.newInput;                
        },
        
        nextSibling(){
            return this.$parent.newProve;                
        },

        lastSibling(){
            return this.$parent.newProve;                
        },
	},
	
	created(){
	},
	
	updated(){
	},
	
	data(){
		return {
			editor: null,
			focus: true,
			theme: 'eclipse',
			hash: null,
		};
	},
	
	methods: {
	},
	
	mounted: codeMirror.mounted,
}
</script>

<style>
</style>