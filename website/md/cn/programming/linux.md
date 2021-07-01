# <center> Linux环境配置

## 终端配置

我主要使用SecureCRTPortable作为访问linux和在linux环境下调试工程代码的工具。  
参考网址：  
https://www.cnblogs.com/zlslch/p/5844479.html  
修改home,end,delete等键盘键，使其与windowns一致：  


![keyMap](linux/keyMap.png)   

其中keyMapCustomed.key是自定义的key文件。
参考网址：

https://blog.csdn.net/need_er/article/details/17753481  
END = \033[4~  
HOME = \033[1~  
DELETE= \033[3~  
utf8编码问题,应作以下配置:  


![utf8](linux/utf8.png)   


如果CRT经常掉线：(automatic logout)  

![logout](linux/logout.png)   

修改文件夹权限：  
chmod -R 777 /home/zlz/python3/  
修改终端背景色：  

![background-color](linux/background-color.png)   


## 查看liux版本

https://blog.csdn.net/huosenbulusi/article/details/85763189

cat /proc/version  
uname -a  
uname -r  
lsb_release -a  
cat /etc/issue  
cat /etc/*release*  
getconf LONG_BIT  
（用于查看32位还是64位）  
对于CentOS系统：  
cat /etc/redhat-release  
参考网址：  
https://blog.csdn.net/comeoncomputer/article/details/78659033  


## 修改环境变量
参考网址：  
https://www.cnblogs.com/hust-chenming/p/4943268.html  
vim ~/.bashrc  
#在最后一行添加：  
export PATH=/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/root/bin  
source ~/.bashrc  

## 日志查看grep
cat -n ../log/error8000.txt | grep "now is the time =" | more  
获取日志行号，比如27119 ，然后输入：  
more +27119 ../log/error8000.txt  

grep -B 2 "^”接地" /mnt/nas/bert_poc_data/H/desc_h_background_data.txt | more  

## SFTP数据传输
如果出现SFTP不能连接问题：  
vi /etc/ssh/sshd_config   
将  
 #Subsystem       sftp    /usr/libexec/openssh/sftp-server  
改为  
Subsystem       sftp    /usr/libexec/openssh/sftp-server  

## 阿里云服务器端口配置方法

[云解析 DNS (aliyun.com)](https://dns.console.aliyun.com/?spm=5176.2020520101.nav-right.2.368a4df5yF8Fo2#/dns/domainList)

进入阿里云服务器配置网站  
https://ecs.console.aliyun.com/#/server/region/cn-shanghai


![aliyun](linux/aliyun.png)   


![aliyun2](linux/aliyun2.png)   


![aliyun3](linux/aliyun3.png)   


![aliyun4](linux/aliyun4.png)   

![aliyun5](linux/aliyun5.png)   

域名购买：  
https://domain.console.aliyun.com/index.htm#/buyer/demandInfoList  
https://dc.console.aliyun.com/next/index#/domain/list/all-domain  

域名备案：  
https://beian.aliyun.com/pcContainer/myorder  
域名证书下载；  
https://dc.console.aliyun.com/next/index#/domain/details/cert-print?saleId=S20208O1A4N63433&domain=axiom.top  


软件著作权  
https://tm.aliyun.com/channel/copyright/new?spm=a2cmq.17629970.0.0.f0d079fe3HRL3T  
