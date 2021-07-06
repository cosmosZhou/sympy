sed -i -E 's/#(LoadModule ssl_module modules\/mod_ssl.so)/\1/' /usr/local/httpd/conf/httpd.conf

sleep 1

sed -i -E 's/#(Include conf\/extra\/httpd-ssl.conf)/\1/' /usr/local/httpd/conf/httpd.conf

sleep 1

sed -i -E 's/#(RewriteRule .+)/\1/' /usr/local/httpd/conf/httpd.conf

sleep 1

/usr/local/httpd/bin/apachectl -k restart