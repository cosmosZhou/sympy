<title>summary</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';

function section($axiom)
{
    list ($section,) = explode('.', $axiom, 2);
    return $section;
}

$repertoire = [];

foreach (\mysql\select_axiom_by_state_not('proved') as $tuple) {
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

<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src="https://unpkg.com/vue@3.2.11/dist/vue.global.prod.js"></script>
<script src="https://cdn.jsdelivr.net/npm/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>
<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>

<script type=module>    
createApp('axiomSummary', {
		state_count_pairs : <?php echo \std\jsonify($state_count_pairs)?>,
		repertoire : <?php echo \std\jsonify($repertoire)?>,
});

</script>
