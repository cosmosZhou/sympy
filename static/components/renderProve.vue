<template>
    <textarea name=prove[]>{{text}}</textarea>
</template>

<script>
console.log('importing renderProve.vue');
import codeMirror from "./codeMirror.vue";

export default {
    props : [ 'text', 'index'],
    
    created(){
        this.$parent.renderProve[this.index] = this;
    },
    
    updated(){
    },
    
    computed:{
    	user: codeMirror.computed.user,
    	module: codeMirror.computed.module,
        
        firstSibling(){
            return this.$parent.renderProve[0];                
        },
        
        nextSibling(){
            return this.$parent.renderProve[this.index + 1];                
        },

        previousSibling(){
            if (this.index == 0) {
	            return this.$parent.$refs.apply;
	        }
            return this.$parent.renderProve[this.index - 1];                
        },
        
        lastSibling(){
            var prove = this.$parent.renderProve;
            return prove[prove.length - 1];                
        },        
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
};
</script>

<style>
.cm-s-indent {
	margin-left: 2.2em;
}
</style>