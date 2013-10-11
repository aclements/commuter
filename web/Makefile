O := dist

EMPTY :=
SPACE := $(EMPTY) $(EMPTY)

.PHONY: all
all:

$O/img/logo.svg: mklogo
	@mkdir -p $(@D)
	./mklogo > $@

$O/img/%.png: %.svg
	@mkdir -p $(@D)
	inkscape -e $@ $^

$O/favicon.ico: $O/img/logo.svg
	@mkdir -p $(@D)
	inkscape -e .logo-16.png -w 16 $^
	inkscape -e .logo-128.png -w 128 $^
	convert .logo-16.png -gravity center -background none -extent 16x16 .logo-16.png
	convert .logo-128.png -gravity center -background none -extent 128x128 .logo-128.png
	./png2ico -o $@ .logo-16.png .logo-128.png
	rm .logo-16.png .logo-128.png

# Link any other file in to $O.
$O/%: %
	@mkdir -p $(@D)
	ln -t $(@D) $^

# The following symlinks files instead of hard-linking them, but
# Firefox will helpfully follow the symlink, breaking all relative
# references.  The make magic constructs a relative path from $@ to $^
# by replacing all directory names in $@ with '..'.
#	ln -t $(@D) $(subst $(SPACE),/,$(patsubst %,..,$(subst /, ,$(@D))))/$^

# Likewise for files from viewer
$O/js/%.js: ../viewer/%.js
	@mkdir -p $(@D)
	ln -t $(@D) $^
$O/css/%.css: ../viewer/%.css
	@mkdir -p $(@D)
	ln -t $(@D) $^

# Copy paper databases
$(MSCAN_DIR)/mscan-xv6.out $(MSCAN_DIR)/mscan-linux.out $(MSCAN_DIR)/model.out:
	@echo "Please set \$$MSCAN_DIR or generate $@"
	@false
$O/sosp13-data.tar.gz: $(MSCAN_DIR)/mscan-xv6.out $(MSCAN_DIR)/mscan-linux.out \
	  $(MSCAN_DIR)/model.out
	@mkdir -p $(@D)
	tar caf $@ --xform 's,.*/,sosp13-data/,' $^

# Generate viewer databases
$O/data/sv6.json: $(MSCAN_DIR)/mscan-xv6.out
	@mkdir -p $(@D)
	../viewer/mkdb --details -o $O/data $< sv6
$O/data/Linux.json: $(MSCAN_DIR)/mscan-linux.out
	@mkdir -p $(@D)
	../viewer/mkdb --details -o $O/data $< Linux

all: $O/index.html
all: $O/img/logo.svg $O/img/model.png $O/img/test.png $O/img/improve.png
all: $O/favicon.ico
all: $O/clements-commutativity-sosp13.pdf
all: $O/sosp13-data.tar.gz
all: $(addprefix $O/,$(wildcard css/*))
all: $(addprefix $O/,$(wildcard img/*))
all: $(addprefix $O/,$(wildcard js/*))
all: $(addprefix $O/,$(wildcard fonts/*))

# Viewer files
all: $O/js/viewer.js $O/css/viewer.css $O/js/linq.min.js
all: $O/data/sv6.json $O/data/Linux.json

# Manual rule to convert fonts.  Requires Fontforge.
fonts/myicon.woff fonts/myicon.ttf: fonts/myicon.svg
	./convfont.pe $^

# Pre-compress files for serving from amsterdam's Apache 1.x
precompress-1.x:
	for f in $O/css/*.css; do gzip --best -c $$f > $$f.gz; done
	cp htaccess-1.x $O/css/.htaccess
	for f in $O/js/*.js; do gzip --best -c $$f > $$f.gz; done
	cp htaccess-1.x $O/js/.htaccess
	for f in $O/data/*.json; do gzip --best -c $$f > $$f.gz; done
	cp htaccess-1.x $O/data/.htaccess

deploy:
	rsync -az --progress dist/ am.lcs:/home/am0/httpd/htdocs/commuter/

clean:
	rm -rf $O
