# <center> Oracle操作指南

Linux报错  
DPI-1047: Cannot locate a 64-bit Oracle Client library: "libclntsh.so: cannot open shared object file: No such file or directory". 
https://oracle.github.io/odpi/doc/installation.html#linux  
下载地址：  
https://download.csdn.net/download/u012424891/9261013  

mkdir -p /opt/oracle   
cd /opt/oracle   
unzip instantclient-basic-linux.x64-11.2.0.4.0.zip  
yum install libaio  
sudo sh -c "echo /opt/oracle/instantclient_11_2 > /etc/ld.so.conf.d/oracle-instantclient.conf"  
sudo ldconfig  

Windows报错:  
DPI-1047: Cannot locate a 64-bit Oracle Client library: "The specified module could not be found".   
https://oracle.github.io/odpi/doc/installation.html#windows  
https://download.csdn.net/download/u014646662/10927017  
解压下载文件生成文件夹：  


![install](oracle/install.png)   

添加D:\Program Files\instantclient_12_2到环境变量path;  


![Path](oracle/Path.png)   