<template>
	<div tabindex=1 @keydown=keydown>
		the whole math theory is composed of the following sections:
 
		<search-form v-if="issearch"></search-form>		
		<ul>
			<li v-for="(content, section) in repertoire">
				<a :href="'/%s/axiom.php/%s'.format(user, section)">
					{{section}}
				</a>
				<ul>
					<li v-for="(axioms, state) in content">
						<font :class=state>
							theorems {{state}}:
						</font>
						<ul>
							<li v-for="axiom in axioms">
								<a :href="'/%s/axiom.php/%s'.format(user, axiom.replace(/\./g, '/'))">
									{{axiom}}
								</a>
							</li>
						</ul>
					</li>
				</ul>
			</li>
		</ul>
		<br>
		in summary, the following is the total count of each state for all theorems:
		<br>
		<table align=left border=1>
	
			<tr>
				<th>state</th>
				<th>count</th>
			</tr>
	
			<tr v-for="tuple of state_count_pairs">
				<td>{{tuple.state}}</td>
				<td>{{tuple.count}}</td>
			</tr>
	
		</table>
	
	</div>
</template>

<script>
	console.log('importing axiom-summary.vue');
	
	const searchForm = httpVueLoader('/sympy/vue/search-form.vue');
	module.exports = {
		components: {searchForm},
		
		props : ['state_count_pairs', 'repertoire'],
		
		computed: {
			user(){
				return sympy_user();
			},
		},
		
		data(){
			return {
				issearch: false,				
			};
		},

		methods: {
			keydown(event){
				console.log("keydown(event){ in axiom-summary.vue");
				switch(event.key){
				case 'f':
					if (event.ctrlKey){
						this.issearch = true;
						event.preventDefault();
						
						this.$nextTick(()=>{
							promise(()=>{
								$("input[type=text]")[0].focus();
							});
						});
					}
				}
			},
		},
	};
</script>

<style scoped>
table{
	margin-left: 4em;
}

div:focus{
	outline: none;
}

font.slow{
	color: yellow;
}

font.failed{
	color: red;
}

font.unprovable{
	color: green;
}

font.plausible{
	color: red;
}

font.unproved{
	color: purple;
}

</style>