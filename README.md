# SymPy

to avoid php websites to show .py files, add the following codes to 
D:\wamp64\bin\apache\apache2.4.39\conf\httpd.conf for windows.

<Files ~ ".py|.pyc">
Order allow,deny
Deny from all
</Files>

<Directory ~ "__pycache__">
Order allow,deny
Deny from all
</Directory>