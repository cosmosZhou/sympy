from util import utility, MySQL


if __name__ == '__main__':
    
    data = []
    user = utility.user
    for axiom, *_ in MySQL.instance.select(f"select axiom from tbl_axiom_py where user = '{user}'"):
        phrases = axiom.split('.')
        size = len(phrases)
        phrases.append('apply')

        prefix = ''

        for i in range(0, size):
            prefix += phrases[i] + "."
            data.append([
                user,
                prefix,
                phrases[i + 1],
                1
            ])
            
            data.append([
                user,
                "axiom." + prefix,
                phrases[i + 1],
                1
            ])

    for sec in ['algebra', 'sets', 'calculus', 'discrete', 'geometry', 'keras', 'stats']:
        data.append([
            user,
            'axiom.',
            sec,
            1
        ])
    
    MySQL.instance.execute(f"delete from tbl_suggest_py where user = '{user}'")    
    MySQL.instance.load_data('tbl_suggest_py', data)

#exec(open('./util/suggest.py').read())