<title>summary</title>
<?php
require_once 'utility.php';
require_once 'searchBox.php';
require_once 'mysql.php';

function section($axiom)
{
    list ($section,) = explode('.', $axiom, 2);
    return $section;
}

$repertoire = [];

foreach (\mysql\select_axiom_by_state_not('success') as $tuple) {
    list ($axiom, $state) = $tuple;
    $repertoire[section($axiom)][$state][] = $axiom;
}

$state_count_pairs = [];

global $user;
foreach (\mysql\select("select state, count(*) as count from tbl_axiom_py where user = '$user' group by state order by count", MYSQLI_ASSOC) as $res) {
    $state_count_pairs[] = $res;
}

$state_count_pairs[] = [
    'state' => 'total',
    'count' => \mysql\select_count()
];
?>
the whole math theory is composed of the following sections:
<div id=root>
	<ul>
		<li v-for="(content, section) in repertoire"><a
			:href="'/%s/axiom.php/%s'.format(user, section)">{{section}}</a>
			<ul>
				<li v-for="(axioms, state) in content"><font :color="colors[state]">theorems
						{{state}}:</font>
					<ul>
						<li v-for="axiom in axioms"><a
							:href="'/%s/axiom.php/%s'.format(user, axiom.replace(/\./g, '/'))">{{axiom}}</a>
						</li>
					</ul></li>
			</ul></li>
	</ul>
	<br>in summary, the following is the total count of each state for all
	theorems:<br>
	<table style='margin-left: 4em;' align=left border=1>

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

<script
	src="https://cdn.jsdelivr.net/npm/jquery@3.4.1/dist/jquery.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="/sympy/js/std.js"></script>
<script src="/sympy/js/utility.js"></script>
<script>
	var data = {
		state_count_pairs : <?php echo \std\jsonify($state_count_pairs)?>,
		repertoire : <?php echo \std\jsonify($repertoire)?>,
		user : <?php echo \std\jsonify($user)?>,
		colors: {
		    failure: 'red',
		    unprovable: 'green',
		    plausible: 'red',
		    insurmountable: 'blue',
		    success: 'blue'
		}			
	};

	var app = new Vue({
		el : '#root',
		data : data, 
	});

	$("input[type=text]")[0].focus();
</script>
