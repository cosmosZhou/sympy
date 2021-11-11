<template>
    <textarea name=apply>{{text}}</textarea>
</template>

<script>
console.log('importing renderApply.vue');
import codeMirror from "./codeMirror.vue";

export default {
    props : [ 'text'],
    
    created(){
    	var hash = location.hash;
    	if (hash){
    		this.hash = hash.slice(1);	
    	}
    },
    
    updated(){
    },
    
    computed: {
    	user: codeMirror.computed.user,
    	module: codeMirror.computed.module,
        
    	firstSibling(){
            return this;                
        },
        
        nextSibling(){
            return this.$parent.renderProve[0];
        },
        
        lastSibling(){
            var prove = this.$parent.renderProve;
            return prove[prove.length - 1];                
        },        
    },
    
    data(){
        return {
            editor: null,
            theme: 'eclipse',
            focus: true,
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