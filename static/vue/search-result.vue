<template>
	<div>
	<search-form :keyword=keyword :regular-expression=regularExpression :whole-word=wholeWord :case-sensitive=caseSensitive></search-form>
	
	search results:<br>
	in all, there are {{modules.length}} hits:
		<br>
		<ul>
	    	<li v-for="module of modules" />
	    		<search-link :module=module></search-link>
	    	</li>
		</ul>
	</div>
</template>

<script>
	console.log('importing search-result.vue');
	var searchForm = httpVueLoader('static/vue/search-form.vue');
	var searchLink = httpVueLoader('static/vue/search-link.vue');
	module.exports = {		
		components: {searchForm, searchLink},
		
		props : [
			'modules',
			'keyword',
			'caseSensitive',			
			'wholeWord',			
			'regularExpression',			
		],

		computed: {
		},
		
		methods: {
		},		
	};
</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>