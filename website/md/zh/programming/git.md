# <center> Git操作指南

## 安装git
windows下参考以下网址：  
https://jingyan.baidu.com/article/a3aad71a0b7249b1fb009608.html  

在linux下:  
输入which git 查看git是否安装  


## git clone

git使用设置
git config --global user.email "chenlizhibeing@126.com"  
git config --global user.name "Cosmos"  
使用get clone获取源代码：  
cd /root/solution  
git clone https://cosmosZhou:######qrup@github.com/cosmosZhou/Python.git  
如果出现  

fatal: unable to access  
https://cosmosZhou:######ok@github.com/cosmosZhou/Python.git/:   
SSL connect error  
输入以下指令：  
yum update -y nss curl libcurl  
参考网址：  
https://blog.csdn.net/lixuande19871015/article/details/80420940  


## git pull

如果git pull报错：  
error: The following untracked working tree files would be overwritten by merge:  
如图：  

解决方法：  
git clean -d -fx  
git pull  
参考网址：  
http://www.mamicode.com/info-detail-2356781.html  

error: Your local changes to the following files would be overwritten by merge:  

Git stash  
Git pull  

eclipse中同步代码PULL报错checkout conflict with files的解决方法:  
1.Team--->Synchronize Workspace  
2.在同步窗口找到冲突文件，把自己本地修改的复制出来  
3.在文件上右键选择 Overwrite----->Yes ,  
4.再次在冲突文件上右键选中 mark as merged  
5.再把复制出来的自己修改的内容与当前内容合并  
6.再切回Package Explorer界面(C-F8)再次PULL。Success!  


## 代码回退
查看可用的回退版本：  
git log --pretty=oneline 

假设Id = 4235569b9dd132a0257856c60ec729883acf5a38  
git reset --hard 4235569b9dd132a0257856c60ec729883acf5a38  

参考网址：
https://blog.csdn.net/ccorg/article/details/80115408

放弃本地修改的改法  ----这种方法会丢弃本地修改的代码，而且不可找回  
git reset --hard  
git pull  
或者  
git fetch --all   
git reset --hard origin/master  


## 切换分支
查看所有分支:  
git branch -a   

创建分支  
git branch develop  
切换到分支develop:  
git checkout develop  

git checkout -b release.1.0.6-Fixing-LRUCache-Bugs  
表示
git branch release.1.0.6-Fixing-LRUCache-Bugs  
git checkout release.1.0.6-Fixing-LRUCache-Bugs  

查看当前分支：  
git branch  

合并master到当前分支：  
git merge master  

提交develop代码：  
git push origin develop  

从master上拉取代码。  
git pull origin master  

## 新建release分支
git checkout release.1.0.10
git branch release.1.0.11
git checkout release.1.0.11
git push --set-upstream origin release.1.0.11