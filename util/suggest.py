# from axiom import MySQL, utility
from util import utility, MySQL


if __name__ == '__main__':
    
    data = []
    user = utility.user
    for axiom, *_ in MySQL.instance.select("select axiom from tbl_axiom_py"):
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

#     sql = '''\
#         CREATE TABLE `tbl_suggest_py` (
#           `user` varchar(32) NOT NULL,
#           `prefix` varchar(256) NOT NULL,
#           `phrase` varchar(32) NOT NULL,
#           `usage` int default 1,
#           PRIMARY KEY (`user`, `prefix`, `phrase`)
#         ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
#         PARTITION BY KEY () PARTITIONS 8;
#     '''
#     try:
#         MySQL.instance.execute(sql)
#     except Exception as e:
#         print(e)
    
    MySQL.instance.load_data('tbl_suggest_py', data)
