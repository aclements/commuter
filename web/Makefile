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
$O/data/%: ../viewer/data/%
	@mkdir -p $(@D)
	ln -t $(@D) $^

all: $O/index.html
all: $O/img/logo.svg $O/img/model.png $O/img/test.png $O/img/improve.png
all: $O/favicon.ico
all: $O/clements-commutativity-sosp13.pdf
all: $(addprefix $O/,$(wildcard css/*))
all: $(addprefix $O/,$(wildcard img/*))
all: $(addprefix $O/,$(wildcard js/*))
all: $(addprefix $O/,$(wildcard fonts/*))

# Viewer files
all: $O/js/viewer.js $O/css/viewer.css $O/js/linq.min.js
all: $(addprefix $O/data/,sv6.json sv6-details.json Linux.json Linux-details.json)
all: $(addprefix $O/,$(subst ../viewer/,,$(wildcard ../viewer/data/template-*)))

# Manual rule to convert fonts.  Requires Fontforge.
fonts/myicon.woff fonts/myicon.ttf: fonts/myicon.svg
	./convfont.pe $^

clean:
	rm -rf $O
