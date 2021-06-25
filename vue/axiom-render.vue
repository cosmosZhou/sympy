<template>
	<div>
		<form name="form" spellcheck=false enctype="multipart/form-data"
			method="post" action="">
			<template v-for="(p, i) in p">
				<template v-if="i == indexOfImply">
					<hr>
					<h3 title='callee hierarchy'>
						<a style='font-size: inherit'
							:href="'/%s/php/hierarchy.php?callee=%s'.format(user, module)"><font
							color=blue>{{inputs[i]}}:</font></a>
					</h3>
				</template>
				<template v-else>
					<textarea name=prove[]>{{inputs[i]}}</textarea>
				</template>
	
				<p>{{p}}</p>
			</template>
	
			<template v-for="(_, i) in inputs.length - p.length">
				<textarea name=prove[]>{{inputs[i + p.length]}}</textarea>
				<br>
			</template>
	
		</form>
	
		<template v-if="logs.length != 0">
			<br> <br>
			<h3>debugging information is printed as follows:</h3>
		</template>
		
		<template v-for="log in logs">
			<p v-if="typeof log == 'string'">{{log}}</p>
			<font v-else class=error>
				{{log.code}}<br>
				{{log.type}}:{{log.error}}<br>
			</font>
		</template>
			
	</div>
</template>

<script>
	console.log('importing axiom-render.vue');
	module.exports = {
		props : [ 'p', 'inputs', 'logs', 'indexOfImply', 'user', 'module'],

		data(){
			return {				
			};		
		},
		
		methods: {
			click(event){
				console.log("click(event){");
			},			
		},		
	};
</script>

<style scoped>
.error {
	colr: red;
}
</style>