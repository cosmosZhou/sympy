import mysql.connector
import re

import random
import configparser
import time

import os
from util.std import json_encode, eol_convert

class Database:

    def create_database(self):
        cursor = self.cursor
        try:
            cursor.execute("CREATE DATABASE {} DEFAULT CHARACTER SET 'utf8'".format(self.DB_NAME))
        except Exception as err:
            print("Failed creating database: {}".format(err))

    def __init__(self):
        conf = configparser.ConfigParser()
        conf.read(os.path.dirname(os.path.dirname(__file__)) + '/config.ini')
        kwargs = conf['client']
        
        try:
            self.conn = mysql.connector.connect(**kwargs)
        except mysql.connector.errors.ProgrammingError as err:
            print(err.msg)
            m = re.compile("Unknown database '(\w+)'").search(err.msg)
            assert m
            database = m[1]
            assert kwargs['database'] == database
            kwargs['database'] = 'mysql'
            self.conn = mysql.connector.connect(**kwargs)
            self.cursor.execute("create database " + database)
            kwargs['database'] = database
            self.conn = mysql.connector.connect(**kwargs)

        except Exception as e:
            print(type(e), e)

    @property
    def cursor(self):
        return self.conn.cursor()

    @property
    def wait_timeout(self):
        cursor = self.cursor
        cursor.execute("show global variables like 'wait_timeout'")
        for Variable_name, Value in cursor:
            assert Variable_name == 'wait_timeout'
            return Value

    @property
    def max_allowed_packet(self):
        cursor = self.cursor
        cursor.execute("show global variables like 'max_allowed_packet'")
        for Variable_name, Value in cursor:
            assert Variable_name == 'max_allowed_packet'
            return Value

    def commit(self):
        self.conn.commit()

    def select(self, sql, rand=None, limit=None):
        if rand:
            sql += " order by rand()"
            
        if limit:
            sql += ' limit %s' % limit

        cursor = self.cursor
        cursor.execute(sql)
        yield from cursor

    def execute(self, sql, *args):
        cursor = self.cursor
        cursor.execute(sql, *args)
        self.commit()
        return cursor.rowcount

    def executemany(self, sql, seq_params):
        cursor = self.cursor
        cursor.executemany(sql, seq_params)
        self.commit()
        return cursor.rowcount

    def show_create_table(self, table):
        for _, sql in self.select("show create table %s" % table):
            return sql

    def show_tables(self):
        tables = [table for table, *_ in self.select("show tables")]
#         tables.sort()
        return tables

    def show_create_table_oracle(self, table):
        for _, sql in self.select("select table_name, dbms_metadata.get_ddl('TABLE','%s') from dual,user_tables where table_name='%s'" % (table, table)):
            return sql

    def desc_oracle(self, table):
        return [args for args in self.select("select column_name,data_type,nullable from all_tab_columns where owner='%s' and table_name='%s'" % (self.conn._con._kwargs['user'], table))]

    def desc_table(self, table):
        return [*self.select("desc %s" % table)]


class MySQLConnector(Database):

    def __init__(self):
        Database.__init__(self)
        
    def load_data_from_list(self, table, array, step=10000, replace=False, ignore=False, truncate=False):
        desc = self.desc_table(table)
        
        has_training_field = False
        
        char_length = [256] * len(desc)
        for i, (Field, Type, *_) in enumerate(desc):
            Type = str(Type, encoding="utf-8")  
            if Field == 'training':
                has_training_field = True
                
            if Type == 'text':
                char_length[i] = 65535
                continue
            m = re.compile("varchar\((\d+)\)").match(Type)
            if m:
                char_length[i] = int(m[1])           
                
        def create_csv(lines, step):
            import tempfile
            folder = tempfile.gettempdir()
                
            for i in range(0, len(lines), step):
                csv = folder + '/%s-%d.csv' % (table, i)
                with open(csv, 'w', encoding='utf8') as file:
                    for args in lines[i:i + step]: 
                        if isinstance(args, tuple):
                            args = [*args]
                            
                        for i, arg in enumerate(args):
                            if isinstance(arg, set):
                                arg = [*arg]
                                                            
                            if isinstance(arg, (list, tuple)):
                                arg = json_encode(arg)
                            elif isinstance(arg, str): 
                                arg = json_encode(arg)[1:-1]
                            else:
                                arg = str(arg)
                            
                            if not ignore and len(arg.encode(encoding='utf8')) > char_length[i]:
                                if truncate:
                                    print('truncating the data to maximum length:', char_length[i], ", since its length is", len(arg.encode(encoding='utf8')))
                                    arg = arg[:char_length[i]]
                                else:
                                    print(args)
                                    print('args[%d] exceeds the allowable length %d' % (i, char_length[i]))
                                    args = None
                                    break
                            assert not arg or arg[-1] != '\r', arg 
                            args[i] = arg
                        
                        if args:
                            if has_training_field:
                                args.append(str(random.randint(0, 1)))               
                            print('\t'.join(args), file=file)
                            
                eol_convert(csv)
                yield csv
                
        for csv in create_csv(array, step):
            self.load_data_from_csv(table, csv, delete=True, replace=replace, ignore=ignore)                

    def load_data(self, table, data, **kwargs):
        if isinstance(data, str):
            self.load_data_from_csv(table, data, **kwargs)
        else:
            self.load_data_from_list(table, data, **kwargs)
            
    def load_data_from_csv(self, table, csv, delete=False, replace=False, ignore=False):
        start = time.time()
        csv = csv.replace('\\', '/')        
        if replace:
            sql = 'load data local infile "%s" replace into table %s character set utf8' % (csv, table)
        elif ignore:
            sql = 'load data local infile "%s" ignore into table %s character set utf8' % (csv, table)
        else: 
            sql = 'load data local infile "%s" into table %s character set utf8' % (csv, table)
        print('executing: ', sql)
        
        local_infile = True
        for Variable_name, Value in self.select("show global variables like 'local_infile'"):
            assert Variable_name == 'local_infile'
            if Value == 'OFF':
                local_infile = False
                
        if not local_infile:
            self.execute('set global local_infile = 1')
            
# in my.ini:            
# [mysql]
# local-infile=1
# 
# [mysqld]
# local-infile=1
            
        try:
            self.execute(sql)
        except Exception as e:
            print(e)
            return        
            
        print('time cost =', (time.time() - start))
        if delete:
            print("os.remove(csv)", csv)
            try:
                os.remove(csv)
            except:
                exit()


instance = MySQLConnector()

    
def select_axiom_lapse_from_tbl_axiom_py(user='root'):
    try:
        return {axiom: lapse for axiom, lapse in instance.select("select axiom, lapse from tbl_axiom_py where user='%s'" % user)}
    except mysql.connector.errors.ProgrammingError as err:
        print(err.msg)
        m = re.compile("Table '(\w+)\.([\w_]+)' doesn't exist").search(err.msg)
        assert m
        assert m[1] == 'axiom'
        assert m[2] == 'tbl_axiom_py'
        sql = '''\
CREATE TABLE `tbl_axiom_py` (
  `user` varchar(32) NOT NULL,
  `axiom` varchar(256) NOT NULL,  
  `state` enum('proved', 'failed', 'plausible', 'unproved', 'unprovable', 'slow') NOT NULL,
  `lapse` double default NULL,  
  `latex` text NOT NULL,
  PRIMARY KEY (`user`, `axiom`) 
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
        sql = '''\
CREATE TABLE `tbl_hierarchy_py` (
  `user` varchar(32) NOT NULL,
  `caller` varchar(256) NOT NULL,
  `callee` varchar(256) NOT NULL,
  `count` int DEFAULT '0',
  PRIMARY KEY (`user`,`caller`,`callee`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
                  
        sql = '''\
CREATE TABLE `tbl_hint_py` (
  `prefix` varchar(36) NOT NULL,
  `phrase` varchar(36) NOT NULL,
  `usage` int DEFAULT '1',
  PRIMARY KEY (`prefix`,`phrase`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
              
        sql = '''\
CREATE TABLE `tbl_suggest_py` (
  `user` varchar(32) NOT NULL,
  `prefix` varchar(256) NOT NULL,
  `phrase` varchar(32) NOT NULL,
  `usage` int DEFAULT '1',
  PRIMARY KEY (`user`,`prefix`,`phrase`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
                
        sql = '''\
CREATE TABLE `tbl_login_py` (
  `user` varchar(32) NOT NULL,
  `password` varchar(32) NOT NULL,
  `email` varchar(128) NOT NULL,
  `port` int DEFAULT '0',
  `visibility` enum('public','private','protected') NOT NULL,
  PRIMARY KEY (`user`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
        
        sql = "insert into tbl_login_py values('sympy', '123456', 'chenlizhibeing@126.com', 'protected')"
        instance.execute(sql)
        
        sql = '''\
CREATE TABLE `tbl_debug_py` (  
  `symbol` varchar(64) NOT NULL,
  `script` text NOT NULL,
  `latex` text NOT NULL,
  PRIMARY KEY (`symbol`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4  
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
        
        sql = '''\
CREATE TABLE `tbl_function_py` (
  `user` varchar(32) NOT NULL,
  `caller` varchar(256) NOT NULL,
  `callee` varchar(256) NOT NULL,
  `func` varchar(64) NOT NULL,
  PRIMARY KEY (`user`,`caller`,`callee`)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci 
PARTITION BY KEY () 
PARTITIONS 8
'''
        instance.execute(sql)
        
        sql = '''\
CREATE TABLE `tbl_breakpoint_py` (
  `user` varchar(32) NOT NULL,
  `module` varchar(256) NOT NULL,  
  `line` int NOT NULL,
  PRIMARY KEY (`user`, `module`, `line`) 
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY () PARTITIONS 8
'''
        instance.execute(sql)
        
    except Exception as e:
        print(type(e), e)
        
    return {}


user = os.path.basename(os.path.dirname(os.path.dirname(__file__)))


def select_axiom_by_state_not(state):
    yield from instance.select(f"select axiom, state from tbl_axiom_py where user = '{user}' and state != '{state}'")


def select_count(state=None):
    sql = f"select count(*) from tbl_axiom_py where user = '{user}'"
    if state:
        sql += f" and state = '{state}'"

    [[count]] = instance.select(sql)
    return count


if __name__ == '__main__':
    ...

#ln -s /usr/local/mysql/mysql.sock /tmp/mysql.sock
#mysql -uroot -p123456 -Daxiom