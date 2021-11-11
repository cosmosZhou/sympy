<template>
	<div tabindex=1 @keydown=keydown>
		the whole math theory is composed of the following sections:
 
		<search-form v-if="issearch"></search-form>		
		<ul>
			<li v-for="(content, section) in repertoire">
				<a :href="'/%s/axiom.php?module=%s'.format(user, section)">
					{{section}}
				</a>
				<ul>
					<li v-for="(axioms, state) in content">
						<font :class=state>
							theorems {{state}}:
						</font>
						<ul>
							<li v-for="axiom in axioms">
								<a :href="'/%s/axiom.php?module=%s'.format(user, axiom)">
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
		<table tabindex=align=left border=1>
	
			<tr>
				<th>state</th>
				<th>count</th>
			</tr>
	
			<tr v-for="tuple of state_count_pairs">
				<td><a :href="state_href(tuple.state)">{{tuple.state}}</a></td>
				<td>{{tuple.count}}</td>
			</tr>	
		</table>
		most recent <input size=2 v-model=topk @change=change_input>axioms updated:
		<a v-for="axiom of recentAxioms" :href="'/%s/axiom.php?module=%s'.format(user, axiom)">
			<p>{{axiom}}</p>
		</a>
		<br>
	</div>
</template>

<script>
console.log('importing axiomSummary.vue');
	
import searchForm from "./searchForm.vue"
	
export default {
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
			recentAxioms: [],
			topk: 10,
		};
	},

	created(){
		this.updateRecentAxioms();
	},
	
	methods: {
		state_href(state){
			if (state == 'total'){
				return `/${this.user}/run.py`;
			}
			return `/${this.user}/axiom.php?state=${state}`;
		},
	
		keydown(event){
			switch(event.key){
			case 'f':
			case 'F':
				if (event.ctrlKey){
					this.issearch = true;
					event.preventDefault();
				}
			}
		},
		
		async updateRecentAxioms(){
			this.recentAxioms = await form_get(`php/request/recent.php?top=${this.topk}`);;
		},
		
		change_input(event){
			this.updateRecentAxioms();
		},
	},
	
	mounted(){
		var failed = document.querySelector('a[href$=failed]') || 
		document.querySelector('a[href$=plausible]')  || 
		document.querySelector('a[href$=unproved]') || 
		document.querySelector('a[href$=unprovable]') || 
		document.querySelector('a[href$=slow]');
		if (failed){
			failed.focus();
		}
	},
}
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