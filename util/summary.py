from util.search import section
from util.MySQL import select_axiom_by_state_not, instance, select_count
from _collections import defaultdict
from util.utility import user, cout

def summary():    
    repertoire = defaultdict(dict)
    
    for axiom, state in select_axiom_by_state_not('proved'):
        try:
            repertoire[section(axiom)][state].append(axiom)
        except KeyError:
            repertoire[section(axiom)][state] = [axiom]
    # print(repertoire)
    repertoire = dict(**repertoire)
    
    state_count_pairs = []
    
    for state, count in instance.select(f"select state, count(*) as count from tbl_axiom_py where user = '{user}' group by state order by count"):
        state_count_pairs.append({'state': state, 'count': count})
    
    state_count_pairs.append({
        'state': 'total',
        'count': select_count()
    })
    
    cout << f'''
<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">    
<title>summary</title>
<div id=root>
 	<axiom-summary :state_count_pairs=state_count_pairs :repertoire=repertoire></axiom-summary>
</div>

<script src="https://cdn.jsdelivr.net/npm/axios/dist/axios.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/qs/dist/qs.js"></script>

<script src="https://cdn.jsdelivr.net/npm/vue@2.6.12/dist/vue.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/http-vue-loader@1.4.2/src/httpVueLoader.min.js"></script>
<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>
<script>
	var data = {{
		state_count_pairs : {state_count_pairs},
		repertoire : {repertoire},
	}};

	Vue.use(httpVueLoader);
	Vue.component('axiom-summary', 'url:static/vue/axiom-summary.vue');
		
	var app = new Vue({{
		el : '#root',
		data : data, 
	}});
</script>
'''