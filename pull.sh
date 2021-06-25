sed -i 's/LoadModule ssl_module modules\/mod_ssl.so/#LoadModule ssl_module modules\/mod_ssl.so/' /usr/local/httpd/conf/httpd.conf

sed -i 's/Include conf\/extra\/httpd-ssl.conf/#Include conf\/extra\/httpd-ssl.conf/' /usr/local/httpd/conf/httpd.conf

sed -i -E 's/RewriteRule (.+)/#RewriteRule \1/' /usr/local/httpd/conf/httpd.conf

/usr/local/httpd/bin/apachectl -k restart

git pull

sed -i 's/#LoadModule ssl_module modules\/mod_ssl.so/LoadModule ssl_module modules\/mod_ssl.so/' /usr/local/httpd/conf/httpd.conf

sed -i 's/#Include conf\/extra\/httpd-ssl.conf/Include conf\/extra\/httpd-ssl.conf/' /usr/local/httpd/conf/httpd.conf

sed -i -E 's/#RewriteRule (.+)/RewriteRule \1/' /usr/local/httpd/conf/httpd.conf

/usr/local/httpd/bin/apachectl -k restart