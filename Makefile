.POSIX:

NAME = webdump
VERSION = 0.1

# paths
PREFIX = /usr/local
MANPREFIX = ${PREFIX}/man
DOCPREFIX = ${PREFIX}/share/doc/${NAME}

RANLIB = ranlib

# use system flags.
WEBDUMP_CFLAGS = ${CFLAGS}
WEBDUMP_LDFLAGS = ${LDFLAGS}
WEBDUMP_CPPFLAGS = -D_DEFAULT_SOURCE -D_XOPEN_SOURCE=700 -D_BSD_SOURCE

BIN = ${NAME}
SCRIPTS =

SRC = ${BIN:=.c}
HDR = arg.h namedentities.h xml.h

LIBXML = libxml.a
LIBXMLSRC = \
	xml.c
LIBXMLOBJ = ${LIBXMLSRC:.c=.o}

COMPATSRC = \
	strlcat.c\
	strlcpy.c
COMPATOBJ =\
	strlcat.o\
	strlcpy.o

LIB = ${LIBXML} ${COMPATOBJ}

MAN1 = ${BIN:=.1}\
	${SCRIPTS:=.1}

DOC = \
	LICENSE\
	README

all: ${BIN}

${BIN}: ${LIB} ${@:=.o}

OBJ = ${SRC:.c=.o} ${LIBXMLOBJ} ${COMPATOBJ}

${OBJ}: ${HDR}

.o:
	${CC} ${WEBDUMP_LDFLAGS} -o $@ $< ${LIB}

.c.o:
	${CC} ${WEBDUMP_CFLAGS} ${WEBDUMP_CPPFLAGS} -o $@ -c $<

${LIBXML}: ${LIBXMLOBJ}
	${AR} rc $@ $?
	${RANLIB} $@

dist:
	rm -rf "${NAME}-${VERSION}"
	mkdir -p "${NAME}-${VERSION}"
	cp -f ${MAN1} ${DOC} ${HDR} \
		${SRC} ${LIBXMLSRC} ${COMPATSRC} ${SCRIPTS} \
		Makefile \
		"${NAME}-${VERSION}"
	# make tarball
	tar -cf - "${NAME}-${VERSION}" | \
		gzip -c > "${NAME}-${VERSION}.tar.gz"
	rm -rf "${NAME}-${VERSION}"

clean:
	rm -f ${BIN} ${OBJ} ${LIB}

install: all
	# installing executable files and scripts.
	mkdir -p "${DESTDIR}${PREFIX}/bin"
	cp -f ${BIN} ${SCRIPTS} "${DESTDIR}${PREFIX}/bin"
	for f in ${BIN} ${SCRIPTS}; do chmod 755 "${DESTDIR}${PREFIX}/bin/$$f"; done
	# installing example files.
	mkdir -p "${DESTDIR}${DOCPREFIX}"
	cp -f README "${DESTDIR}${DOCPREFIX}"
	# installing manual pages for general commands: section 1.
	mkdir -p "${DESTDIR}${MANPREFIX}/man1"
	cp -f ${MAN1} "${DESTDIR}${MANPREFIX}/man1"
	for m in ${MAN1}; do chmod 644 "${DESTDIR}${MANPREFIX}/man1/$$m"; done

uninstall:
	# removing executable files and scripts.
	for f in ${BIN} ${SCRIPTS}; do rm -f "${DESTDIR}${PREFIX}/bin/$$f"; done
	# removing example files.
	rm -f "${DESTDIR}${DOCPREFIX}/README"
	-rmdir "${DESTDIR}${DOCPREFIX}"
	# removing manual pages.
	for m in ${MAN1}; do rm -f "${DESTDIR}${MANPREFIX}/man1/$$m"; done

.PHONY: all clean dist install uninstall
