# Serve pre-compressed files if present and possible
AddEncoding gzip .gz
RewriteEngine on
RewriteCond %{HTTP:Accept-encoding} gzip
#RewriteCond %{HTTP_USER_AGENT} !Safari
RewriteCond %{REQUEST_FILENAME}\.gz -f
RewriteRule ^(.*)$ $1.gz [QSA,L]
