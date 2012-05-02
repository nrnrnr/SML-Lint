SMLNJHOME=/usr/lib/smlnj
SUFFIX=`$SMLNJHOME/bin/.arch-n-opsys | sed 's/.*HEAP_SUFFIX=//'`
SRC=`find * -name '*.sml' -o -name '*.sig'`

test:V:
	sml <<'EOF'
	CM.make "lint.cm";
	Lint.parse "top.sml";
	EOF

ltest:V:
	sml <<'EOF'
	CM.make "lint.cm";
	Lint.parse "lint.sml";
	EOF

lint:V: lint.$SUFFIX

lint.$SUFFIX: $SRC
	ml-build lint.cm Lint.run lint

install:V: $LIB/lint.$SUFFIX
$LIB/lint.$SUFFIX: lint.$SUFFIX
	cp -av $prereq $target

