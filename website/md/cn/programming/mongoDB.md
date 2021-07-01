# <center> mongoDB操作指南

curl -O https://fastdl.mongodb.org/linux/mongodb-linux-x86_64-3.0.6.tgz # 下载   
or  
curl -O https://fastdl.mongodb.org/linux/mongodb-linux-x86_64-3.6.4.tgz # 下载   

tar -zxvf mongodb-linux-x86_64-3.6.4.tgz # 解压   
mv mongodb-linux-x86_64-3.6.4/ ~/mongodb # 将解压包拷贝到指定目录  
mongod -logpath /data/db/mongo.log -logappend -fork -port 27017 -bind_ip 0.0.0.0  
sudo mkdir -p /data/db  
sudo chmod -Rf 777 /data/db  

Start mongo server:  
mongod -shutdown  

Run mongodb script:  
mongo  
mongo --version  

Reference:  
https://www.runoob.com/mongodb/mongodb-linux-install.html  
https://www.mongodb.com/download-center/community  