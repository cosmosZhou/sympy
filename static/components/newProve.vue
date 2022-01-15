<template>
	<textarea name=prove>{{text}}</textarea>
</template>

<script>
console.log('importing newProve.vue');
import codeMirror from "./codeMirror.vue";

export default {
	props : ['text'],
	
	computed:{
        firstSibling(){
            return this.$parent.newApply;                
        },
        
        previousSibling(){
        	return this.$parent.newApply;
        },
        
        lastSibling(){
            return this;                
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
			theme: 'eclipse indent',
			hash: null,
		};
	},
	
	methods: {
		EqVariables: codeMirror.methods.EqVariables,
	},

	mounted: codeMirror.mounted,
}
</script>

<style>
.cm-s-indent {
	margin-left: 2.2em;
}
</style>