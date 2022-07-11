<template>
	<searchForm :keyword=keyword :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive></searchForm>
	search results:
	<br>
	in all, there are {{modules.length}} hits:
	<br>
	<ul>
    	<li v-for="module of modules">
    		<searchLink :module=module></searchLink>
    	</li>
	</ul>
</template>

<script>
console.log('importing searchResult.vue');
import searchForm from "./searchForm.vue"
import searchLink from "./searchLink.vue"

export default {
	components: {searchForm, searchLink},

	props : ['modules', 'keyword', 'caseSensitive', 'wholeWord', 'regularExpression'],

	computed: {
	},

	methods: {
	},		
}

</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>