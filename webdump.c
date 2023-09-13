#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>

#include "arg.h"
char *argv0;

#include "xml.h"

static XMLParser parser;

#ifndef __OpenBSD__
#define pledge(p1,p2) 0
#endif

#undef strlcat
size_t strlcat(char *, const char *, size_t);
#undef strlcpy
size_t strlcpy(char *, const char *, size_t);

/* ctype-like macros, but always compatible with ASCII / UTF-8 */
#define ISALPHA(c) ((((unsigned)c) | 32) - 'a' < 26)
#define ISCNTRL(c) ((c) < ' ' || (c) == 0x7f)
#define ISDIGIT(c) (((unsigned)c) - '0' < 10)
#define ISSPACE(c) ((c) == ' ' || ((((unsigned)c) - '\t') < 5))
#define TOLOWER(c) ((((unsigned)c) - 'A' < 26) ? ((c) | 32) : (c))

#define LEN(x) (sizeof(x) / sizeof(x[0]))

/* URI */
struct uri {
	char proto[48];     /* scheme including ":" or "://" */
	char userinfo[256]; /* username [:password] */
	char host[256];
	char port[6];       /* numeric port */
	char path[1024];
	char query[1024];
	char fragment[1024];
};

/* options */
static int allowansi     = 0;  /* allow ANSI escape codes */
static int showrefbottom = 0;  /* show link references at the bottom */
static int showrefinline = 0;  /* show link reference number inline */
static int showurlinline = 0;  /* show full link reference inline */
static int linewrap      = 0;  /* line-wrapping */
static int termwidth     = 77; /* terminal width */
static int resources     = 0;  /* write resources line-by-line to fd 3? */
static int uniqrefs      = 0;  /* number unique references */

/* linked-list of link references */
struct linkref {
	char *type;
	char *url;
	int ishidden;
	size_t linknr;
	struct linkref *next;
};

static struct linkref *links_head;
static struct linkref *links_cur;
static int linkcount; /* visible link count */

enum DisplayType {
	DisplayUnknown     = 0,
	DisplayInline      = 1 << 0,
	DisplayInlineBlock = 1 << 1, /* unused for now */
	DisplayBlock       = 1 << 2,
	DisplayNone        = 1 << 3,
	DisplayPre         = 1 << 4,
	DisplayList        = 1 << 5,
	DisplayListOrdered = 1 << 6,
	DisplayListItem    = 1 << 7,
	DisplayTable       = 1 << 8,
	DisplayTableRow    = 1 << 9,
	DisplayTableCell   = 1 << 10,
	DisplayHeader      = 1 << 11,
	DisplayDl          = 1 << 12,
	DisplayInput       = 1 << 13,
	DisplayButton      = 1 << 14,
	DisplaySelect      = 1 << 15,
	DisplaySelectMulti = 1 << 16,
	DisplayOption      = 1 << 17
};

/* ANSI markup */
enum MarkupType {
	MarkupNone        = 0,
	MarkupBold        = 1 << 0,
	MarkupItalic      = 1 << 1,
	MarkupUnderline   = 1 << 2,
	MarkupBlink       = 1 << 3, /* lol */
	MarkupReverse     = 1 << 4,
	MarkupStrike      = 1 << 5
};

/* String data / memory pool */
typedef struct string {
	char   *data;   /* data */
	size_t  len;    /* string length */
	size_t  bufsiz; /* allocated size */
} String;

struct tag {
	const char *name;
	enum DisplayType displaytype;
	enum MarkupType markuptype; /* ANSI markup */
	enum DisplayType parenttype; /* display type belonging to element */
	int isvoid; /* "void" element */
	int isoptional; /* optional to close tag */
	int margintop; /* newlines when the tag starts */
	int marginbottom; /* newlines after the tag ends */
	int indent; /* indent in cells */
};

struct node {
	char tagname[256];
	struct tag tag;
	size_t nchildren; /* child node count */
	size_t visnchildren; /* child node count which are visible */
	/* attributes */
	char id[256];
	char classnames[1024];
	int indent; /* indent per node, for formatting */
	int hasdata; /* tag contains some data, for formatting */
};

struct selectornode {
	char tagname[256];
	long index; /* index of node to match on: -1 if not matching on index */
	/* attributes */
	char id[256];
	char classnames[1024];
};

struct selector {
	const char *text;
	struct selectornode nodes[32];
	int depth;
};

/* list of selectors */
struct selectors {
	struct selector **selectors;
	size_t count;
};

static const char *str_bullet_item = "* ";
static const char *str_checkbox_checked = "x";
static const char *str_ruler = "-";
static const char *str_radio_checked = "*";

/* base href, to make URLs absolute */
static char *basehref = "";
static char basehrefdoc[4096]; /* base href in document, if any */
static int basehrefset = 0; /* base href set and can be used? */
static struct uri base;

/* buffers for some attributes of the current tag */
String attr_alt; /* alt attribute */
String attr_checked; /* checked attribute */
String attr_class; /* class attribute */
String attr_data; /* data attribute */
String attr_href; /* href attribute */
String attr_id; /* id attribute */
String attr_src; /* src attribute */
String attr_type; /* type attribute */
String attr_value; /* value attribute */

static String htmldata;

/* for white-space output handling:
   1 = whitespace emitted (suppress repeated), 2 = other characters on this line
   Behaviour:
   * White-space data before non-whitespace data in tags are ignored on a line.
   * Repeated white-space are ignored: a single space (' ') is emitted.
*/
static int whitespace_mode = 0;
static int nbytesline = 0;
static int ncells = 0; /* current cell count */
static int hadnewline = 0; /* count for repeated newlines */
/* flag for skipping initial white-space in tag: for HTML white-space handling */
static int skipinitialws = 1;
#define DEFAULT_INDENT 2
static const int defaultindent = DEFAULT_INDENT;
static int indent;
/* previous output sequential newlines, used for calculating margins between
   elements and reducing excessive newlines */
static int currentnewlines;

/* buffers for line-wrapping (buffer per word boundary) */
static char rbuf[1024];
static int rbuflen;
static int rnbufcells = 0; /* pending cell count to add */

#define MAX_DEPTH 256
static struct node nodes[MAX_DEPTH];
static String nodes_links[MAX_DEPTH]; /* keep track of links per node */
static int curnode;

/* reader / selector mode */
static int reader_mode = 0;
static int reader_ignore = 0;

static enum MarkupType curmarkup;

/* selector to match */
static struct selectors *sel_hide, *sel_show;

/* tag          displaytype                       markup           parent           v  o  b  a  i */
static struct tag tags[] = {
{ "a",          DisplayInline,                    MarkupUnderline, 0,               0, 0, 0, 0, 0 },
{ "address",    DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "area",       DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "article",    DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "aside",      DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "audio",      DisplayInline,                    MarkupUnderline, 0,               0, 0, 0, 0, 0 },
{ "b",          DisplayInline,                    MarkupBold,      0,               0, 0, 0, 0, 0 },
{ "base",       DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "blink",      DisplayInline,                    MarkupBlink,     0,               0, 0, 0, 0, 0 },
{ "blockquote", DisplayBlock,                     0,               0,               0, 0, 0, 0, 2 },
{ "body",       DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "br",         0,                                0,               0,               1, 0, 0, 0, 0 },
{ "button",     DisplayInline | DisplayButton,    0,               0,               0, 0, 0, 0, 0 },
{ "cite",       DisplayInline,                    MarkupItalic,    0,               0, 0, 0, 0, 0 },
{ "col",        DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "colgroup",   DisplayInline,                    0,               0,               0, 1, 0, 0, 0 },
{ "datalist",   DisplayNone,                      0,               0,               0, 0, 0, 0, 0 },
{ "dd",         DisplayBlock,                     0,               0,               0, 1, 0, 0, 4 },
{ "del",        DisplayInline,                    MarkupStrike,    0,               0, 0, 0, 0, 0 },
{ "details",    DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "dfn",        DisplayInline,                    MarkupItalic,    0,               0, 0, 0, 0, 0 },
{ "dir",        DisplayList,                      0,               0,               0, 0, 1, 1, 2 },
{ "div",        DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "dl",         DisplayBlock | DisplayDl,         0,               0,               0, 0, 0, 0, 0 },
{ "dt",         DisplayBlock,                     MarkupBold,      0,               0, 1, 0, 0, 0 },
{ "em",         DisplayInline,                    MarkupItalic,    0,               0, 0, 0, 0, 0 },
{ "embed",      DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "fieldset",   DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "figcaption", DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "figure",     DisplayBlock,                     0,               0,               0, 0, 1, 1, 4 },
{ "footer",     DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "form",       DisplayBlock,                     0,               0,               0, 0, 0, 1, 0 },
{ "h1",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "h2",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "h3",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "h4",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "h5",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "h6",         DisplayHeader,                    MarkupBold,      0,               0, 0, 1, 1, -DEFAULT_INDENT },
{ "head",       DisplayBlock,                     0,               0,               0, 1, 0, 0, 0 },
{ "header",     DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "hr",         DisplayBlock,                     0,               0,               1, 0, 0, 0, 0 },
{ "html",       DisplayBlock,                     0,               0,               0, 1, 0, 0, 0 },
{ "i",          DisplayInline,                    MarkupItalic,    0,               0, 0, 0, 0, 0 },
{ "img",        DisplayInline,                    MarkupUnderline, 0,               1, 0, 0, 0, 0 },
{ "input",      DisplayInput,                     0,               0,               1, 0, 0, 0, 0 },
{ "ins",        DisplayInline,                    MarkupUnderline, 0,               0, 0, 0, 0, 0 },
{ "label",      DisplayInline,                    0,               0,               0, 0, 0, 0, 0 },
{ "legend",     DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "li",         DisplayListItem,                  0,               DisplayList,     0, 1, 0, 0, 0 },
{ "link",       DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "main",       DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "mark",       DisplayInline,                    MarkupReverse,   0,               0, 0, 0, 0, 0 },
{ "menu",       DisplayList,                      0,               0,               0, 0, 1, 1, 2 },
{ "meta",       DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "nav",        DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "object",     DisplayInline,                    0,               0,               0, 0, 0, 0, 0 },
{ "ol",         DisplayList | DisplayListOrdered, 0,               0,               0, 0, 1, 1, 0 },
{ "option",     DisplayInline | DisplayOption,    0,               0,               0, 1, 0, 0, 0 },
{ "p",          DisplayBlock,                     0,               0,               0, 1, 1, 1, 0 },
{ "param",      DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "pre",        DisplayPre,                       0,               0,               0, 0, 1, 1, 4 },
{ "s",          DisplayInline,                    MarkupStrike,    0,               0, 0, 0, 0, 0 },
{ "search",     DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "script",     DisplayNone,                      0,               0,               0, 0, 0, 0, 0 },
{ "section",    DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "select",     DisplayInline | DisplaySelect,    0,               0,               0, 0, 0, 0, 0 },
{ "source",     DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "strike",     DisplayInline,                    MarkupStrike,    0,               0, 0, 0, 0, 0 },
{ "strong",     DisplayInline,                    MarkupBold,      0,               0, 0, 0, 0, 0 },
{ "style",      DisplayNone,                      0,               0,               0, 0, 0, 0, 0 },
{ "summary",    DisplayBlock,                     0,               0,               0, 0, 0, 0, 0 },
{ "table",      DisplayTable,                     0,               0,               0, 0, 0, 0, 0 },
{ "tbody",      DisplayInline,                    0,               DisplayTable,    0, 1, 0, 0, 0 },
{ "td",         DisplayTableCell,                 0,               DisplayTableRow, 0, 1, 0, 0, 0 },
{ "template",   DisplayNone,                      0,               0,               0, 0, 0, 0, 0 },
{ "textarea",   DisplayInline,                    0,               0,               0, 0, 0, 0, 0 },
{ "tfoot",      DisplayInline,                    0,               DisplayTable,    0, 1, 0, 0, 0 },
{ "th",         DisplayTableCell,                 MarkupBold,      DisplayTableRow, 0, 1, 0, 0, 0 },
{ "thead",      DisplayInline,                    0,               DisplayTable,    0, 1, 0, 0, 0 },
{ "title",      DisplayBlock,                     0,               0,               0, 0, 0, 1, -DEFAULT_INDENT },
{ "tr",         DisplayTableRow,                  0,               DisplayTable,    0, 1, 0, 0, 0 },
{ "track",      DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "u",          DisplayInline,                    MarkupUnderline, 0,               0, 0, 0, 0, 0 },
{ "ul",         DisplayList,                      0,               0,               0, 0, 1, 1, 2 },
{ "var",        DisplayInline,                    MarkupItalic,    0,               0, 0, 0, 0, 0 },
{ "video",      DisplayInline,                    MarkupUnderline, 0,               0, 0, 0, 0, 0 },
{ "wbr",        DisplayInline,                    0,               0,               1, 0, 0, 0, 0 },
{ "xmp",        DisplayPre,                       0,               0,               0, 0, 1, 1, 4 }
};

/* hint for compilers and static analyzers that a function exits */
#ifndef __dead
#define __dead
#endif

/* print to stderr, print error message of errno and exit(). */
__dead void
err(int exitstatus, const char *fmt, ...)
{
	va_list ap;
	int saved_errno;

	saved_errno = errno;

	fputs("webdump: ", stderr);
	if (fmt) {
		va_start(ap, fmt);
		vfprintf(stderr, fmt, ap);
		va_end(ap);
		fputs(": ", stderr);
	}
	fprintf(stderr, "%s\n", strerror(saved_errno));

	exit(exitstatus);
}

/* print to stderr and exit(). */
__dead void
errx(int exitstatus, const char *fmt, ...)
{
	va_list ap;

	fputs("webdump: ", stderr);
	if (fmt) {
		va_start(ap, fmt);
		vfprintf(stderr, fmt, ap);
		va_end(ap);
	}
	fputs("\n", stderr);

	exit(exitstatus);
}

static const char *ignorestate, *endtag;
static int (*getnext)(void);

/* return a space for all data until some case-insensitive string occurs. This
   is used to parse incorrect HTML/XML that contains unescaped HTML in script
   or style tags. If you see some </script> tag in a CDATA or comment
   section then e-mail W3C and tell them the web is too complex. */
static inline int
getnext_ignore(void)
{
	int c;

	if ((c = getnext()) == EOF)
		return EOF;

	if (TOLOWER((unsigned char)c) == TOLOWER((unsigned char)*ignorestate)) {
		ignorestate++;
		if (*ignorestate == '\0') {
			parser.getnext = getnext; /* restore */
			return ' ';
		}
	} else {
		ignorestate = endtag; /* no full match: reset to beginning */
	}

	return ' '; /* pretend there is just SPACEs */
}

/* Clear string only; don't free, prevents unnecessary reallocation. */
static void
string_clear(String *s)
{
	if (s->data)
		s->data[0] = '\0';
	s->len = 0;
}

static void
string_buffer_realloc(String *s, size_t newlen)
{
	size_t alloclen;

	for (alloclen = 64; alloclen <= newlen; alloclen *= 2)
		;
	if (!(s->data = realloc(s->data, alloclen)))
		err(1, "realloc");
	s->bufsiz = alloclen;
}

static void
string_append(String *s, const char *data, size_t len)
{
	if (!len)
		return;
	/* check if allocation is necesary, don't shrink buffer,
	 * should be more than bufsiz ofcourse. */
	if (s->len + len >= s->bufsiz)
		string_buffer_realloc(s, s->len + len + 1);
	memcpy(s->data + s->len, data, len);
	s->len += len;
	s->data[s->len] = '\0';
}

char *
estrdup(const char *s)
{
	char *p;

	if (!(p = strdup(s)))
		err(1, "strdup");
	return p;
}

char *
estrndup(const char *s, size_t n)
{
	char *p;

	if (!(p = strndup(s, n)))
		err(1, "strndup");
	return p;
}

void *
erealloc(void *p, size_t siz)
{
	if (!(p = realloc(p, siz)))
		err(1, "realloc");

	return p;
}

void *
ecalloc(size_t nmemb, size_t size)
{
	void *p;

	if (!(p = calloc(nmemb, size)))
		err(1, "calloc");
	return p;
}

/* check if string has a non-empty scheme / protocol part */
int
uri_hasscheme(const char *s)
{
	const char *p = s;

	for (; ISALPHA((unsigned char)*p) || ISDIGIT((unsigned char)*p) ||
		       *p == '+' || *p == '-' || *p == '.'; p++)
		;
	/* scheme, except if empty and starts with ":" then it is a path */
	return (*p == ':' && p != s);
}

int
uri_parse(const char *s, struct uri *u)
{
	const char *p = s;
	char *endptr;
	size_t i;
	long l;

	u->proto[0] = u->userinfo[0] = u->host[0] = u->port[0] = '\0';
	u->path[0] = u->query[0] = u->fragment[0] = '\0';

	/* protocol-relative */
	if (*p == '/' && *(p + 1) == '/') {
		p += 2; /* skip "//" */
		goto parseauth;
	}

	/* scheme / protocol part */
	for (; ISALPHA((unsigned char)*p) || ISDIGIT((unsigned char)*p) ||
		       *p == '+' || *p == '-' || *p == '.'; p++)
		;
	/* scheme, except if empty and starts with ":" then it is a path */
	if (*p == ':' && p != s) {
		if (*(p + 1) == '/' && *(p + 2) == '/')
			p += 3; /* skip "://" */
		else
			p++; /* skip ":" */

		if ((size_t)(p - s) >= sizeof(u->proto))
			return -1; /* protocol too long */
		memcpy(u->proto, s, p - s);
		u->proto[p - s] = '\0';

		if (*(p - 1) != '/')
			goto parsepath;
	} else {
		p = s; /* no scheme format, reset to start */
		goto parsepath;
	}

parseauth:
	/* userinfo (username:password) */
	i = strcspn(p, "@/?#");
	if (p[i] == '@') {
		if (i >= sizeof(u->userinfo))
			return -1; /* userinfo too long */
		memcpy(u->userinfo, p, i);
		u->userinfo[i] = '\0';
		p += i + 1;
	}

	/* IPv6 address */
	if (*p == '[') {
		/* bracket not found, host too short or too long */
		i = strcspn(p, "]");
		if (p[i] != ']' || i < 3)
			return -1;
		i++; /* including "]" */
	} else {
		/* domain / host part, skip until port, path or end. */
		i = strcspn(p, ":/?#");
	}
	if (i >= sizeof(u->host))
		return -1; /* host too long */
	memcpy(u->host, p, i);
	u->host[i] = '\0';
	p += i;

	/* port */
	if (*p == ':') {
		p++;
		if ((i = strcspn(p, "/?#")) >= sizeof(u->port))
			return -1; /* port too long */
		memcpy(u->port, p, i);
		u->port[i] = '\0';
		/* check for valid port: range 1 - 65535, may be empty */
		errno = 0;
		l = strtol(u->port, &endptr, 10);
		if (i && (errno || *endptr || l <= 0 || l > 65535))
			return -1;
		p += i;
	}

parsepath:
	/* path */
	if ((i = strcspn(p, "?#")) >= sizeof(u->path))
		return -1; /* path too long */
	memcpy(u->path, p, i);
	u->path[i] = '\0';
	p += i;

	/* query */
	if (*p == '?') {
		p++;
		if ((i = strcspn(p, "#")) >= sizeof(u->query))
			return -1; /* query too long */
		memcpy(u->query, p, i);
		u->query[i] = '\0';
		p += i;
	}

	/* fragment */
	if (*p == '#') {
		p++;
		if ((i = strlen(p)) >= sizeof(u->fragment))
			return -1; /* fragment too long */
		memcpy(u->fragment, p, i);
		u->fragment[i] = '\0';
	}

	return 0;
}

/* Transform and try to make the URI `u` absolute using base URI `b` into `a`.
   Follows some of the logic from "RFC 3986 - 5.2.2. Transform References".
   Returns 0 on success, -1 on error or truncation. */
int
uri_makeabs(struct uri *a, struct uri *u, struct uri *b)
{
	char *p;
	int c;

	strlcpy(a->fragment, u->fragment, sizeof(a->fragment));

	if (u->proto[0] || u->host[0]) {
		strlcpy(a->proto, u->proto[0] ? u->proto : b->proto, sizeof(a->proto));
		strlcpy(a->host, u->host, sizeof(a->host));
		strlcpy(a->userinfo, u->userinfo, sizeof(a->userinfo));
		strlcpy(a->host, u->host, sizeof(a->host));
		strlcpy(a->port, u->port, sizeof(a->port));
		strlcpy(a->path, u->path, sizeof(a->path));
		strlcpy(a->query, u->query, sizeof(a->query));
		return 0;
	}

	strlcpy(a->proto, b->proto, sizeof(a->proto));
	strlcpy(a->host, b->host, sizeof(a->host));
	strlcpy(a->userinfo, b->userinfo, sizeof(a->userinfo));
	strlcpy(a->host, b->host, sizeof(a->host));
	strlcpy(a->port, b->port, sizeof(a->port));

	if (!u->path[0]) {
		strlcpy(a->path, b->path, sizeof(a->path));
	} else if (u->path[0] == '/') {
		strlcpy(a->path, u->path, sizeof(a->path));
	} else {
		a->path[0] = (b->host[0] && b->path[0] != '/') ? '/' : '\0';
		a->path[1] = '\0';

		if ((p = strrchr(b->path, '/'))) {
			c = *(++p);
			*p = '\0'; /* temporary NUL-terminate */
			if (strlcat(a->path, b->path, sizeof(a->path)) >= sizeof(a->path))
				return -1;
			*p = c; /* restore */
		}
		if (strlcat(a->path, u->path, sizeof(a->path)) >= sizeof(a->path))
			return -1;
	}

	if (u->path[0] || u->query[0])
		strlcpy(a->query, u->query, sizeof(a->query));
	else
		strlcpy(a->query, b->query, sizeof(a->query));

	return 0;
}

int
uri_format(char *buf, size_t bufsiz, struct uri *u)
{
	return snprintf(buf, bufsiz, "%s%s%s%s%s%s%s%s%s%s%s%s",
		u->proto,
		u->userinfo[0] ? u->userinfo : "",
		u->userinfo[0] ? "@" : "",
		u->host,
		u->port[0] ? ":" : "",
		u->port,
		u->host[0] && u->path[0] && u->path[0] != '/' ? "/" : "",
		u->path,
		u->query[0] ? "?" : "",
		u->query,
		u->fragment[0] ? "#" : "",
		u->fragment);
}

/* compare tag name (case-insensitive) */
int
tagcmp(const char *s1, const char *s2)
{
	return strcasecmp(s1, s2);
}

/* compare attribute name (case-insensitive) */
int
attrcmp(const char *s1, const char *s2)
{
	return strcasecmp(s1, s2);
}

static void
rindent(void)
{
	int i, total;

	total = indent + defaultindent;
	if (total < 0)
		total = 0;
	for (i = 0; i < total; i++)
		putchar(' ');

	nbytesline += total;
	ncells += total;
}

static void
emitmarkup(int markuptype)
{
	if (!allowansi)
		return;

	if (!markuptype)
		fputs("\033[0m", stdout); /* reset all attributes */

	/* set */
	if (markuptype & MarkupBold)
		fputs("\033[1m", stdout);
	if (markuptype & MarkupItalic)
		fputs("\033[3m", stdout);
	if (markuptype & MarkupUnderline)
		fputs("\033[4m", stdout);
	if (markuptype & MarkupBlink)
		fputs("\033[5m", stdout);
	if (markuptype & MarkupReverse)
		fputs("\033[7m", stdout);
	if (markuptype & MarkupStrike)
		fputs("\033[9m", stdout);
}

/* flush remaining buffer (containing a word): used for word-wrap handling */
static void
hflush(void)
{
	int i;

	if (!rbuflen)
		return;

	if (!nbytesline) {
		if (curmarkup)
			emitmarkup(0);
		rindent();
		/* emit code again per line, needed for GNU/less -R */
		if (curmarkup)
			emitmarkup(curmarkup);
	}

	for (i = 0; i < rbuflen; i++)
		putchar(rbuf[i]);

	nbytesline += rbuflen;
	ncells += rnbufcells;
	rbuflen = 0;
	rnbufcells = 0;
}

static void
printansi(const char *s)
{
	size_t len;

	if (!allowansi)
		return;

	if (linewrap) {
		len = strlen(s);
		if (rbuflen + len + 1 >= sizeof(rbuf))
			hflush();
		if (rbuflen + len + 1 < sizeof(rbuf)) {
			memcpy(rbuf + rbuflen, s, len);
			rbuflen += len;
			/* NOTE: nbytesline and ncells are not counted for markup */
		}
	} else {
		fputs(s, stdout);
	}
}

static void
setmarkup(int markuptype)
{
	if (!allowansi)
		return;

	/* need change? */
	if (curmarkup == markuptype)
		return;

	if (!markuptype) {
		printansi("\033[0m"); /* reset all attributes */
		curmarkup = markuptype;
		return;
	}

	/* set */
	if (!(curmarkup & MarkupBold) && (markuptype & MarkupBold))
		printansi("\033[1m");
	if (!(curmarkup & MarkupItalic) && (markuptype & MarkupItalic))
		printansi("\033[3m");
	if (!(curmarkup & MarkupUnderline) && (markuptype & MarkupUnderline))
		printansi("\033[4m");
	if (!(curmarkup & MarkupBlink) && (markuptype & MarkupBlink))
		printansi("\033[5m");
	if (!(curmarkup & MarkupReverse) && (markuptype & MarkupReverse))
		printansi("\033[7m");
	if (!(curmarkup & MarkupStrike) && (markuptype & MarkupStrike))
		printansi("\033[9m");

	/* unset */
	if ((curmarkup & MarkupBold) && !(markuptype & MarkupBold))
		printansi("\033[22m"); /* reset bold or faint */
	if ((curmarkup & MarkupItalic) && !(markuptype & MarkupItalic))
		printansi("\033[23m"); /* reset italic */
	if ((curmarkup & MarkupUnderline) && !(markuptype & MarkupUnderline))
		printansi("\033[24m"); /* reset underline */
	if ((curmarkup & MarkupBlink) && !(markuptype & MarkupBlink))
		printansi("\033[25m"); /* reset blink */
	if ((curmarkup & MarkupReverse) && !(markuptype & MarkupReverse))
		printansi("\033[27m"); /* reset reverse */
	if ((curmarkup & MarkupStrike) && !(markuptype & MarkupStrike))
		printansi("\033[29m"); /* reset strike */

	curmarkup = markuptype;
}

static void
startmarkup(int markuptype)
{
	setmarkup(curmarkup | markuptype);
}

static void
endmarkup(int markuptype)
{
	setmarkup(curmarkup & ~markuptype);
}

/* rough cell width of a unicode codepoint by counting a unicode codepoint as 1
   cell in general.
   NOTE: this is of course incorrect since characters can be 2 width aswell,
   in the future maybe replace this with wcwidth() or similar */
int
utfwidth(int c)
{
	/* not the start of a codepoint */
	if ((c & 0xc0) == 0x80)
		return 0;
	/* count TAB as 8 */
	if (c == '\t')
		return 8;
	return 1;
}

/* write a character, handling state of repeated newlines, some HTML
   white-space rules, indentation and word-wrapping */
static void
hputchar(int c)
{
	struct node *cur = &nodes[curnode];
	cur->hasdata = 1;

	if (c == '\n') {
		/* previous line had characters, so not a repeated newline */
		if (nbytesline > 0)
			hadnewline = 0;

		/* start a new line, no chars on this line yet */
		whitespace_mode &= ~2; /* no chars on this line yet */
		nbytesline = 0;
		ncells = 0;

		if (hadnewline)
			currentnewlines++; /* repeating newlines */
		hadnewline = 1;
	} else {
		hadnewline = 0;
		currentnewlines = 0;
	}

	/* skip initial/leading white-space */
	if (ISSPACE((unsigned char)c)) {
		if (skipinitialws)
			return;
	} else {
		skipinitialws = 0;
	}

	if (!(c == '\n' || c == '\t' || !ISCNTRL((unsigned char)c)))
		return;

	if (!linewrap) {
		if (c == '\n') {
			putchar('\n');
			nbytesline = 0;
			ncells = 0;
		} else {
			if (!nbytesline) {
				if (curmarkup)
					emitmarkup(0);
				rindent();
				/* emit code again per line, needed for GNU/less -R */
				if (curmarkup)
					emitmarkup(curmarkup);
			}
			putchar(c);
			nbytesline++;
			ncells += utfwidth(c);
		}
		return;
	}

	/* really too long: the whole word doesn't even fit, flush it */
	if (ncells + rnbufcells >= termwidth || rbuflen >= sizeof(rbuf) - 1) {
		putchar('\n');
		nbytesline = 0;
		ncells = 0;
		hflush();
	}

	if (c == '\n') {
		putchar('\n');
		hflush();
		return;
	} else if (ISSPACE((unsigned char)c) || c == '-') {
		if (ncells + rnbufcells >= termwidth) {
			putchar('\n');
			nbytesline = 0;
			ncells = 0;
		}
		rbuf[rbuflen++] = c;
		rnbufcells += utfwidth(c);
		hflush();
		return;
	}

	rbuf[rbuflen++] = c;
	rnbufcells += utfwidth(c);
}

/* calculate indentation of current node depth, using the sum of each
   indentation per node */
static int
calcindent(void)
{
	int i, n = 0;

	for (i = curnode; i >= 0; i--)
		n += nodes[i].indent;

	return n;
}

static void
hprint(const char *s)
{
	for (; *s; ++s)
		hputchar(*s);
}

/* printf(), max 256 bytes for now */
static void
hprintf(const char *fmt, ...)
{
	va_list ap;
	char buf[256];

	va_start(ap, fmt);
	vsnprintf(buf, sizeof(buf), fmt, ap);
	va_end(ap);

	/* use hprint() formatting logic. */
	hprint(buf);
}

static void
newline(void)
{
	if (skipinitialws)
		return;
	hputchar('\n');
}

static int
parentcontainerhasdata(int curtype, int n)
{
	int i;

	for (i = n; i >= 0; i--) {
		if (nodes[i].tag.displaytype & (DisplayList|DisplayTable))
			break;
		if (nodes[i].hasdata)
			return 1;
	}

	return 0;
}

static int
parenthasdata(int n)
{
	int i;

	for (i = n; i >= 0; i--)
		return nodes[i].hasdata;

	return 0;
}

/* start on a newline for the start of a block element or not */
static void
startblock(void)
{
	hflush();
	whitespace_mode &= ~2; /* no characters on this line yet */
	if (nbytesline <= 0)
		return;
	if (!hadnewline && parenthasdata(curnode - 1))
		hputchar('\n');
}

/* start on a newline for the end of a block element or not */
static void
endblock(void)
{
	hflush();
	whitespace_mode &= ~2; /* no characters on this line yet */
	if (nbytesline <= 0)
		return;
	if (!hadnewline)
		hputchar('\n');
}

/* print one character safely: no control characters,
   handle HTML white-space rules */
static void
printc(int c)
{
	if (ISSPACE((unsigned char)c)) {
		if (whitespace_mode == 2)
			hputchar(' ');
		whitespace_mode |= 1;
	} else {
		whitespace_mode = 2;
		if (!ISCNTRL((unsigned char)c))
			hputchar(c);
	}
}

static void
printpre(const char *s, size_t len)
{
	struct node *cur;
	size_t i;

	/* reset state of newlines because this data is printed literally */
	hadnewline = 0;
	currentnewlines = 0;

	/* skip leading newline */
	i = 0;
	if (skipinitialws) {
		if (*s == '\n' && i < len) {
			s++;
			i++;
		}
	}

	hflush();

	skipinitialws = 0;

	if (*s) {
		cur = &nodes[curnode];
		cur->hasdata = 1;
	}

	for (; *s && i < len; s++, i++) {
		switch (*s) {
		case '\n':
			putchar('\n');
			nbytesline = 0;
			ncells = 0;
			break;
		case '\t':
			hadnewline = 0;
			if (!nbytesline) {
				if (curmarkup)
					emitmarkup(0);
				rindent();
				/* emit code again per line, needed for GNU/less -R */
				if (curmarkup)
					emitmarkup(curmarkup);
			}

			/* TAB to 8 spaces */
			fputs("        ", stdout);
			nbytesline += 8;
			ncells += 8;
			break;
		default:
			if (ISCNTRL((unsigned char)*s))
				continue;

			if (!nbytesline) {
				if (curmarkup)
					emitmarkup(0);
				rindent();
				/* emit code again per line, needed for GNU/less -R */
				if (curmarkup)
					emitmarkup(curmarkup);
			}

			putchar(*s);
			nbytesline++;
			/* start of rune: incorrectly assume 1 rune is 1 cell for now */
			ncells += utfwidth((unsigned char)*s);
		}
	}
}

static struct node *
findparenttype(int cur, int findtype)
{
	int i;

	for (i = cur; i >= 0; i--) {
		if ((nodes[i].tag.displaytype & findtype))
			return &nodes[i];
	}
	return NULL;
}

int
isclassmatch(const char *haystack, const char *needle)
{
	const char *p;
	size_t needlelen;
	size_t matched = 0;

	needlelen = strlen(needle);
	for (p = haystack; *p; p++) {
		if (ISSPACE((unsigned char)*p)) {
			matched = 0;
			continue;
		}
		if (needle[matched] == *p)
			matched++;
		else
			matched = 0;
		if (matched == needlelen) {
			if (*(p + 1) == '\0' || ISSPACE((unsigned char)*(p + 1)))
				return 1;
		}
	}

	return 0;
}

/* very limited CSS-like selector, supports: main, main#id, main.class,
   ".class", "#id", "ul li a" */
int
compileselector(const char *sel, struct selectornode *nodes, size_t maxnodes)
{
	int depth = 0, len;
	long l;
	const char *s, *start;
	char tmp[256];
	int nameset = 0;

	memset(&nodes[0], 0, sizeof(nodes[0]));
	nodes[0].index = -1;

	s = sel;
	for (; *s && ISSPACE((unsigned char)*s); s++)
		;

	start = s;
	for (; ; s++) {
		/* end of tag */
		if (!nameset &&
		    (*s == '#' || *s == '.' || *s == '@' ||
		     *s == '\0' || ISSPACE((unsigned char)*s))) {
			nameset = 1;
			len = s - start; /* tag name */
			if (len >= sizeof(tmp))
				return 0;
			if (len)
				memcpy(tmp, start, len);
			tmp[len] = '\0';

			memcpy(nodes[depth].tagname, tmp, len + 1);
		}

		/* end */
		if (*s == '\0' || ISSPACE((unsigned char)*s)) {
			for (; ISSPACE((unsigned char)*s); s++)
				;
			start = s; /* start of a new tag */
			depth++;
			if (depth >= maxnodes)
				return 0;

			nameset = 0;
			memset(&nodes[depth], 0, sizeof(nodes[depth]));
			nodes[depth].index = -1;

			/* end of selector */
			if (*s == '\0')
				break;
		}

		/* index */
		if (*s == '@') {
			len = strcspn(s + 1, ".#@ \t\n");
			if (len >= sizeof(tmp))
				return 0;
			memcpy(tmp, s + 1, len);
			tmp[len] = '\0';

			l = strtol(tmp, NULL, 10);
			if (l >= 0)
				nodes[depth].index = l;
			s += len;
			start = s + 1;
			continue;
		}

		/* id */
		if (*s == '#') {
			len = strcspn(s + 1, ".#@ \t\n");
			if (len >= sizeof(tmp))
				return 0;
			memcpy(tmp, s + 1, len);
			tmp[len] = '\0';
			memcpy(nodes[depth].id, tmp, len + 1);
			s += len;
			start = s + 1;
			continue;
		}

		/* class */
		if (*s == '.') {
			len = strcspn(s + 1, ".#@ \t\n");
			if (len >= sizeof(tmp))
				return 0;
			memcpy(tmp, s + 1, len);
			tmp[len] = '\0';
			/* allow only one classname for now */
			memcpy(nodes[depth].classnames, tmp, len + 1);
			s += len;
			start = s + 1;
			continue;
		}
	}

	return depth;
}

struct selector *
newselector(const char *q)
{
	struct selector *sel;
	int r;

	sel = ecalloc(1, sizeof(*sel));
	sel->text = estrdup(q);

	r = compileselector(sel->text, sel->nodes, LEN(sel->nodes));
	if (r <= 0) {
		free(sel);
		return NULL;
	}
	sel->depth = r;

	return sel;
}

struct selectors *
compileselectors(const char *q)
{
	struct selectors *sels = NULL;
	struct selector *sel;
	const char *start;
	char *qe;
	int count = 0;
	size_t siz;

	sels = ecalloc(1, sizeof(*sels));

	start = q;
	for (; ; q++) {
		if (*q == ',' || *q == '\0') {
			qe = estrndup(start, q - start);
			sel = newselector(qe);
			free(qe);

			/* add new selector */
			siz = (count + 1) * sizeof(struct selector *);
			sels->selectors = erealloc(sels->selectors, siz);
			sels->selectors[count] = sel;
			count++;

			if (*q == '\0')
				break;
			start = q + 1;
		}
	}
	sels->count = count;

	return sels;
}

/* very limited CSS-like matcher, supports: main, main#id, main.class,
   ".class", "#id", "ul li a" */
int
iscssmatch(struct selector *sel, struct node *root, int maxdepth)
{
	int d, md = 0;

	for (d = 0; d <= maxdepth; d++) {
		/* tag matched? */
		if (sel->nodes[md].tagname[0] &&
		    strcasecmp(sel->nodes[md].tagname, root[d].tagname))
			continue; /* no */

		/* id matched? */
		if (sel->nodes[md].id[0] && strcmp(sel->nodes[md].id, root[d].id))
			continue; /* no */

		/* class matched, for now allow only one classname in the selector,
		   matching multiple classnames */
		if (sel->nodes[md].classnames[0] &&
		    !isclassmatch(root[d].classnames, sel->nodes[md].classnames))
			continue; /* no */

		/* index matched */
		if (sel->nodes[md].index != -1 &&
		    (d == 0 ||
		    root[d - 1].nchildren == 0 ||
		    sel->nodes[md].index != root[d - 1].nchildren - 1))
			continue;

		md++;
		/* all matched of one selector */
		if (md == sel->depth)
			return 1;
	}

	return 0;
}

int
iscssmatchany(struct selectors *sels, struct node *root, int maxdepth)
{
	struct selector *sel;
	int i;

	for (i = 0; i < sels->count; i++) {
		sel = sels->selectors[i];
		if (iscssmatch(sel, root, maxdepth))
			return 1;
	}
	return 0;
}

static void
handleinlinealt(void)
{
	struct node *cur;
	char *start, *s, *e;

	/* do not show the alt text if the element is hidden */
	cur = &nodes[curnode];
	if (cur->tag.displaytype & DisplayNone)
		return;

	/* show img alt attribute as text. */
	if (attr_alt.len) {
		start = attr_alt.data;
		e = attr_alt.data + attr_alt.len;

		for (s = start; s < e; s++)
			printc((unsigned char)*s);
		hflush();
	}
}

/* slow linear lookup of link references
   TODO: optimize it, maybe using tree.h RB_TREE? */
static struct linkref *
findlinkref(const char *url)
{
	struct linkref *cur;

	for (cur = links_head; cur; cur = cur->next) {
		if (!strcmp(url, cur->url))
			return cur;
	}
	return NULL;
}

static struct linkref *
addlinkref(const char *url, const char *_type, int ishidden, int linknr)
{
	if (!tagcmp(_type, "a"))
		_type = "link";

	/* add to linked list */
	if (!links_head)
		links_cur = links_head = ecalloc(1, sizeof(*links_head));
	else
		links_cur = links_cur->next = ecalloc(1, sizeof(*links_head));
	links_cur->url = estrdup(url);
	links_cur->type = estrdup(_type);
	links_cur->ishidden = ishidden;
	links_cur->linknr = linknr;

	return links_cur;
}

static void
handleinlinelink(void)
{
	struct uri newuri, olduri;
	struct node *cur;
	char buf[4096], *url;
	int r;

	if (!showrefbottom && !showrefinline && !showurlinline && !resources)
		return; /* there is no need to collect the reference */

	if (!attr_href.len && !attr_src.len && !attr_data.len)
		return; /* there is no reference */

	/* by default use the original URL */
	if (attr_src.len)
		url = attr_src.data;
	else if (attr_href.len)
		url = attr_href.data;
	else
		url = attr_data.data;

	if (!url)
		return;

	/* Not an absolute URL yet: try to make it absolute.
	   If it is not possible use the relative URL */
	if (!uri_hasscheme(url) && basehrefset &&
	    uri_parse(url, &olduri) != -1 &&
	    uri_makeabs(&newuri, &olduri, &base) != -1 &&
	    newuri.proto[0]) {
		r = uri_format(buf, sizeof(buf), &newuri);
		if (r >= 0 && (size_t)r < sizeof(buf))
			url = buf;
	}

	if (!url[0])
		return;

	cur = &nodes[curnode];

	if (!(cur->tag.displaytype & DisplayNone)) {
		string_clear(&nodes_links[curnode]);
		string_append(&nodes_links[curnode], url, strlen(url));
	}

	/* add hidden links directly to the reference,
	   the order doesn't matter */
	if (cur->tag.displaytype & DisplayNone)
		addlinkref(url, cur->tag.name, 1, 0);
}

void
printlinkrefs(void)
{
	size_t i;
	int hashiddenrefs = 0;

	if (!links_head)
		return;

	if (resources) {
		for (i = 1, links_cur = links_head; links_cur; links_cur = links_cur->next, i++)
			dprintf(3, "%s\t%s\n", links_cur->type, links_cur->url);
	}

	printf("\nReferences\n\n");

	i = 1;
	for (links_cur = links_head; links_cur; links_cur = links_cur->next) {
		if (links_cur->ishidden) {
			hashiddenrefs = 1;
			continue;
		}
		printf(" %zu. %s (%s)\n", links_cur->linknr, links_cur->url, links_cur->type);
		i++;
	}

	if (hashiddenrefs)
		printf("\n\nHidden references\n\n");
	/* hidden links don't have a link number, just count them */
	for (links_cur = links_head; links_cur; links_cur = links_cur->next) {
		if (!links_cur->ishidden)
			continue;
		printf(" %zu. %s (%s)\n", i, links_cur->url, links_cur->type);
		i++;
	}
}

static void
xmldatastart(XMLParser *p)
{
}

static void
xmldataend(XMLParser *p)
{
	struct node *cur;
	char *start, *s, *e;

	if (!htmldata.data || !htmldata.len)
		return;

	cur = &nodes[curnode];

	if (reader_ignore || (cur->tag.displaytype & DisplayNone)) {
		/* print nothing */
	} else if ((cur->tag.displaytype & DisplayPre) ||
	           findparenttype(curnode - 1, DisplayPre)) {
		printpre(htmldata.data, htmldata.len);
	} else {
		start = htmldata.data;
		e = htmldata.data + htmldata.len;

		for (s = start; s < e; s++)
			printc((unsigned char)*s);
	}

	string_clear(&htmldata);
}

static void
xmldata(XMLParser *p, const char *data, size_t datalen)
{
	struct node *cur;

	if (reader_ignore)
		return;

	cur = &nodes[curnode];
	if (cur->tag.displaytype & DisplayNone)
		return;

	string_append(&htmldata, data, datalen);
}

static void
xmldataentity(XMLParser *p, const char *data, size_t datalen)
{
	struct node *cur;
	char buf[16];
	int n;

	if (reader_ignore)
		return;

	cur = &nodes[curnode];
	if (cur->tag.displaytype & DisplayNone)
		return;

	n = xml_entitytostr(data, buf, sizeof(buf));
	if (n > 0)
		xmldata(p, buf, (size_t)n);
	else
		xmldata(p, data, datalen);
}

static void
xmlcdatastart(XMLParser *p)
{
	xmldatastart(p);
}

static void
xmlcdataend(XMLParser *p)
{
	xmldataend(p); /* treat CDATA as data */
}

static void
xmlcdata(XMLParser *p, const char *data, size_t datalen)
{
	xmldata(p, data, datalen); /* treat CDATA as data */
}

/* lookup function to compare tag name (case-insensitive) for sort functions */
int
findtagcmp(const void *v1, const void *v2)
{
	struct tag *t1 = (struct tag *)v1;
	struct tag *t2 = (struct tag *)v2;

	return strcasecmp(t1->name, t2->name);
}

/* binary search tag by tag name */
struct tag *
findtag(const char *t)
{
	struct tag find = { 0 };

	find.name = t;

	return bsearch(&find, tags, LEN(tags), sizeof(*tags), findtagcmp);
}

static void
handleendtag(struct tag *tag)
{
	int i, marginbottom;

	if (tag->displaytype & DisplayNone)
		return;
	if (reader_ignore)
		return;

	if (tag->displaytype & (DisplayBlock | DisplayHeader | DisplayTable | DisplayTableRow |
		DisplayList | DisplayListItem | DisplayPre)) {
		endblock(); /* break line if needed */
	}

	/* when a list ends and its not inside a list add an extra bottom margin */
	marginbottom = tag->marginbottom;

	if (marginbottom > 0) {
		if (tag->displaytype & DisplayList) {
			if (findparenttype(curnode - 1, DisplayList))
				marginbottom--;
		}
	}

	if (marginbottom > 0) {
		hflush();
		for (i = currentnewlines; i < marginbottom; i++) {
			putchar('\n');
			nbytesline = 0;
			ncells = 0;
			currentnewlines++;
		}
		hadnewline = 1;
	}
}

static void
endnode(struct node *cur)
{
	struct linkref *ref;
	int i, ishidden;

	/* set a flag indicating the element and its parent containers have data.
	   This is used for some formatting */
	if (cur->hasdata) {
		for (i = curnode; i >= 0; i--)
			nodes[i].hasdata = 1;
	}

	endmarkup(cur->tag.markuptype);

	ishidden = reader_ignore || (cur->tag.displaytype & DisplayNone);

	/* add link and show the link number in the visible order */
	if (!ishidden && nodes_links[curnode].len > 0) {
		if (uniqrefs)
			ref = findlinkref(nodes_links[curnode].data);
		else
			ref = NULL;

		/* new link: add it */
		if (!ref) {
			linkcount++;
			ref = addlinkref(nodes_links[curnode].data,
				cur->tag.name, ishidden, linkcount);
		}

		if (showrefinline)
			hprintf("[%zu]", ref->linknr);
		if (showurlinline)
			hprintf(" [%s: %s]", ref->type, ref->url);
		if (showrefinline || showurlinline)
			hflush();
	}

	handleendtag(&(cur->tag));
}

static void
xmltagend(XMLParser *p, const char *t, size_t tl, int isshort)
{
	struct tag *found, *tag;
	char *child, *childs[16];
	size_t nchilds;
	int i, j, k, nchildfound, parenttype;

	/* ignore closing of void elements, like </br>, which is not allowed */
	if ((found = findtag(t))) {
		if (!isshort && found->isvoid)
			return;
	}

	/* TODO: implement more complete optional tag handling.
	   in reality the optional tag rules are more complex, see:
           https://html.spec.whatwg.org/multipage/syntax.html#optional-tags */

	child = NULL;
	nchilds = 0;
	nchildfound = 0;
	parenttype = 0;

	if (found && found->displaytype & DisplayPre) {
		skipinitialws = 0; /* do not skip white-space, for margins */
	} else if (found && found->displaytype & DisplayList) {
		childs[0] = "li";
		nchilds = 1;
		parenttype = DisplayList;
	} else if (found && found->displaytype & DisplayTableRow) {
		childs[0] = "td";
		nchilds = 1;
		parenttype = DisplayTableRow;
	} else if (found && found->displaytype & DisplayTable) {
		childs[0] = "td";
		nchilds = 1;
		parenttype = DisplayTable;
	} else if (found && found->displaytype & DisplayDl) {
		childs[0] = "p";
		childs[1] = "dd";
		childs[2] = "dt";
		nchilds = 3;
		parenttype = DisplayDl;
	}

	if (nchilds > 0) {
		for (i = curnode; i >= 0; i--) {
			if (nchildfound)
				break;
			if ((nodes[i].tag.displaytype & parenttype))
				break;
			for (j = 0; j < nchilds; j++) {
				child = childs[j];
				if (!tagcmp(nodes[i].tag.name, child)) {
					/* fake closing the previous tags */
					for (k = curnode; k >= i; k--)
						endnode(&nodes[k]);
					curnode = k;
					nchildfound = 1;
					break;
				}
			}
		}
	}

	/* if the current closing tag matches the current open tag */
	if (nodes[curnode].tag.name &&
	    !tagcmp(nodes[curnode].tag.name, t)) {
		endnode(&nodes[curnode]);
		if (curnode)
			curnode--;
	} else {
		/* ... else lookup the first matching start tag. This is also
		   for handling optional closing tags */
		tag = NULL;
		for (i = curnode; i >= 0; i--) {
			if (nodes[curnode].tag.name &&
			    !tagcmp(nodes[i].tag.name, t)) {
				endnode(&nodes[i]);
				curnode = i > 0 ? i - 1 : 0;
				tag = &nodes[i].tag;
				break;
			}
		}
		/* unmatched closing tag found */
		if (!tag && found)
			handleendtag(found);
	}
	indent = calcindent();

	/* restore markup of the tag we are in now */
	startmarkup(nodes[curnode].tag.markuptype);

	/* check if the current node still matches the visible selector */
	if (reader_mode && sel_show && !reader_ignore) {
		if (!iscssmatchany(sel_show, nodes, curnode)) {
			reader_ignore = 1;
			newline();
		}
	}
}

static void
xmltagstart(XMLParser *p, const char *t, size_t tl)
{
	struct tag *found;
	struct node *cur;
	char *child, *childs[16];
	size_t nchilds;
	char *s;
	int i, j, k, nchildfound, parenttype;

	if (curnode >= MAX_DEPTH - 2)
		errx(1, "max tag depth reached: %d\n", curnode);

	cur = &nodes[curnode];

	string_clear(&attr_alt);
	string_clear(&attr_checked);
	string_clear(&attr_class);
	string_clear(&attr_data);
	string_clear(&attr_href);
	string_clear(&attr_id);
	string_clear(&attr_src);
	string_clear(&attr_type);
	string_clear(&attr_value);

	/* match tag */
	found = findtag(t);

	/* TODO: implement more complete optional tag handling.
	   in reality the optional tag rules are more complex, see:
           https://html.spec.whatwg.org/multipage/syntax.html#optional-tags */

	child = NULL;
	nchilds = 0;
	nchildfound = 0;
	parenttype = 0;

	/* if optional tag <p> is open and a list element is found, close </p>. */
	if (found && found->displaytype & DisplayList) {
		/* not inside a list */
		childs[0] = "p";
		nchilds = 1;
		parenttype = DisplayList;
	} else if (found && found->isoptional) {
		if (!tagcmp(t, "li")) {
			childs[0] = "li";
			nchilds = 1;
			parenttype = DisplayList;
		} else if (!tagcmp(t, "td")) {
			childs[0] = "td";
			nchilds = 1;
			parenttype = DisplayTableRow;
		} else if (!tagcmp(t, "tr")) {
			childs[0] = "tr";
			nchilds = 1;
			parenttype = DisplayTable;
		} else if (!tagcmp(t, "p")) {
			childs[0] = "p";
			nchilds = 1;
			parenttype = 0; /* seek until the root */
		} else if (!tagcmp(t, "dt")) {
			childs[0] = "dd";
			nchilds = 1;
			parenttype = 0; /* seek until the root */
		} else if (!tagcmp(t, "dd")) {
			childs[0] = "dd";
			childs[1] = "dt";
			nchilds = 2;
			parenttype = 0; /* seek until the root */
		} else if (!tagcmp(t, cur->tag.name)) {
			/* fake closing the previous tag if it is the same and repeated */
			xmltagend(p, t, tl, 0);
		}
	} else if (found && found->displaytype & DisplayBlock) {
		/* check if we have an open "<p>" tag */
		childs[0] = "p";
		childs[1] = "dl";
		nchilds = 2;
		parenttype = 0; /* seek until the root */
	}

	if (nchilds > 0) {
		for (i = curnode; i >= 0; i--) {
			if (nchildfound)
				break;
			if ((nodes[i].tag.displaytype & parenttype))
				break;
			for (j = 0; j < nchilds; j++) {
				child = childs[j];
				if (!tagcmp(nodes[i].tag.name, child)) {
					/* fake closing the previous tags */
					for (k = curnode; k >= i; k--)
						xmltagend(p, nodes[k].tag.name, strlen(nodes[k].tag.name), 0);
					nchildfound = 1;
					break;
				}
			}
		}
	}

	curnode++;
	string_clear(&nodes_links[curnode]); /* clear possible link reference for this node */
	cur = &nodes[curnode];
	memset(cur, 0, sizeof(*cur)); /* clear / reset node */
	/* tag defaults */
	cur->tag.displaytype = DisplayInline;
	cur->tag.name = cur->tagname;
	strlcpy(cur->tagname, t, sizeof(cur->tagname));
	/* force to lowercase */
	for (s = cur->tagname; *s; s++)
		*s = TOLOWER((unsigned char)*s);

	/* matched tag: copy tag information to current node */
	if (found)
		memcpy(&(cur->tag), found, sizeof(*found));

	/* parent tag is hidden, so hide ourself too */
	if (curnode > 0 && (nodes[curnode - 1].tag.displaytype & DisplayNone))
		cur->tag.displaytype |= DisplayNone;
}

static void
xmltagstartparsed(XMLParser *p, const char *t, size_t tl, int isshort)
{
	struct node *cur, *parent;
	int i, margintop;

	/* temporary replace the callback except the reader and end of tag
	   restore the context once we receive the same ignored tag in the
	   end tag handler */
	if (!tagcmp(t, "script")) {
		ignorestate = endtag = "</script>";
		getnext = p->getnext; /* for restore */
		p->getnext = getnext_ignore;
		xmltagend(p, t, tl, 0); /* fake the call the tag was ended */
		return;
	} else if (!tagcmp(t, "style")) {
		ignorestate = endtag = "</style>";
		getnext = p->getnext; /* for restore */
		p->getnext = getnext_ignore;
		xmltagend(p, t, tl, 0); /* fake the call the tag was ended */
		return;
	}

	cur = &nodes[curnode];

	/* copy attributes if set */
	if (attr_id.len)
		strlcpy(cur->id, attr_id.data, sizeof(cur->id));
	else
		cur->id[0] = '\0';
	if (attr_class.len)
		strlcpy(cur->classnames, attr_class.data, sizeof(cur->classnames));
	else
		cur->classnames[0] = '\0';

	/* parent node */
	if (curnode > 0) {
		parent = &nodes[curnode - 1];
		parent->nchildren++; /* increase child node count */
		/* count visible childnodes */
		if (!(cur->tag.displaytype & DisplayNone))
			parent->visnchildren++;
	} else {
		parent = NULL;
	}

	if (reader_mode && sel_show && reader_ignore &&
	    iscssmatchany(sel_show, nodes, curnode))
		reader_ignore = 0;

	/* hide element */
	if (reader_mode && sel_hide &&
	    iscssmatchany(sel_hide, nodes, curnode))
		cur->tag.displaytype |= DisplayNone;

	/* indent for this tag */
	cur->indent = cur->tag.indent;

	if (!reader_ignore) {
		/* add link reference, print links and alt text */
		handleinlinelink();
		handleinlinealt();
	}

	if (cur->tag.displaytype & DisplayNone)
		return;

	if (reader_ignore)
		return;

	indent = calcindent();

	if ((cur->tag.displaytype & (DisplayBlock | DisplayHeader | DisplayPre |
		DisplayTable | DisplayTableRow |
		DisplayList | DisplayListItem))) {
		startblock(); /* break line if needed */
	}

	margintop = cur->tag.margintop;
	if (cur->tag.displaytype & (DisplayList)) {
		for (i = curnode - 1; i >= 0; i--) {
			if (nodes[i].tag.displaytype & DisplayList)
				break;
			if (!(nodes[i].tag.displaytype & DisplayListItem))
				continue;
			if (nodes[i].hasdata && margintop > 0) {
				margintop--;
				break;
			}
		}
	} else if (cur->tag.displaytype & (DisplayBlock|DisplayTable)) {
		if (!parentcontainerhasdata(cur->tag.displaytype, curnode - 1)) {
			if (margintop > 0)
				margintop--;
		}
	}

	if (margintop > 0) {
		hflush();
		for (i = currentnewlines; i < margintop; i++) {
			putchar('\n');
			nbytesline = 0;
			ncells = 0;
			currentnewlines++;
		}
		hadnewline = 1;
	}

	if (cur->tag.displaytype & DisplayPre) {
		skipinitialws = 1;
	} else if (cur->tag.displaytype & DisplayTableCell) {
		if (parent && parent->visnchildren > 1)
			hputchar('\t');
	} else if (cur->tag.displaytype & DisplayListItem) {
		/* find first parent node and ordered numbers or unordered */
		if (parent) {
			skipinitialws = 0;

			/* print bullet, add columns to indentation level */
			if (parent->tag.displaytype & DisplayListOrdered) {
				hprintf("%4zu. ", parent->nchildren);
				cur->indent = 6;
				indent += cur->indent; /* align to number */
			} else if (parent->tag.displaytype & DisplayList) {
				hprint(str_bullet_item);
				cur->indent = 2;
				indent += 2; /* align to bullet */
			}
		}
		skipinitialws = 0;
	} else if (cur->tag.displaytype & DisplayInput) {
		if (!attr_type.len) {
			hprintf("[%-15s]", attr_value.len ? attr_value.data : ""); /* default: text */
		} else if (!strcasecmp(attr_type.data, "button") ||
		           !strcasecmp(attr_type.data, "submit") ||
		           !strcasecmp(attr_type.data, "reset")) {
			hprintf("[%s]", attr_value.len ? attr_value.data : "");
		} else if (!strcasecmp(attr_type.data, "checkbox")) {
			hprintf("[%s]",
				attr_checked.len &&
				!strcasecmp(attr_checked.data, "checked") ? str_checkbox_checked : " ");
		} else if (!strcasecmp(attr_type.data, "radio")) {
			hprintf("[%s]",
				attr_checked.len &&
				!strcasecmp(attr_checked.data, "checked") ? str_radio_checked : " ");
		} else if (!strcasecmp(attr_type.data, "hidden")) {
			cur->tag.displaytype |= DisplayNone;
		} else {
			/* unrecognized / default case is text */
			hprintf("[%-15s]", attr_value.len ? attr_value.data : "");
		}
	}

	startmarkup(cur->tag.markuptype);

	/* do not count data such as an item bullet as part of the data for
	   the node */
	cur->hasdata = 0;

	if (!tagcmp(t, "hr")) { /* ruler */
		i = termwidth - indent - defaultindent;
		for (; i > 0; i--)
			hprint(str_ruler);
		cur->hasdata = 1; /* treat <hr/> as data */
	} else if (!tagcmp(t, "br")) {
		hflush();
		hadnewline = 0; /* forced newline */
		hputchar('\n');
		cur->hasdata = 1; /* treat <br/> as data */
	}

	/* autoclose tags, such as <br>, pretend we are <br/> */
	if (!isshort && cur->tag.isvoid)
		xmltagend(p, t, tl, 1); /* pretend close of short tag */
}

static void
xmlattr(XMLParser *p, const char *tag, size_t taglen, const char *name,
        size_t namelen, const char *value, size_t valuelen)
{
	struct node *cur;

	cur = &nodes[curnode];

	if (!attrcmp(name, "class"))
		string_append(&attr_class, value, valuelen);
	else if (!attrcmp(name, "id"))
		string_append(&attr_id, value, valuelen);

	/* <base href="..." /> */
	if (!basehrefset && !attrcmp(name, "href") && !tagcmp(tag, "base"))
		strlcat(basehrefdoc, value, sizeof(basehrefdoc));

	/* hide tags with attribute aria-hidden or hidden */
	if (!attrcmp(name, "aria-hidden") || !attrcmp(name, "hidden"))
		cur->tag.displaytype |= DisplayNone;

	if (!tagcmp(tag, "a") && !attrcmp(name, "href"))
		string_append(&attr_src, value, valuelen);

	if ((!tagcmp(tag, "img") || !tagcmp(tag, "video") ||
	     !tagcmp(tag, "source") || !tagcmp(tag, "track") ||
	     !tagcmp(tag, "audio")) &&
	    !attrcmp(name, "src") && valuelen)
		string_append(&attr_href, value, valuelen);

	/* show img alt attribute as text. */
	if (!tagcmp(tag, "img") && !attrcmp(name, "alt"))
		string_append(&attr_alt, value, valuelen);

	if (!attrcmp(name, "checked"))
		string_append(&attr_checked, value, valuelen);
	if (!attrcmp(name, "type"))
		string_append(&attr_type, value, valuelen);
	if (!attrcmp(name, "value"))
		string_append(&attr_value, value, valuelen);
}

static void
xmlattrentity(XMLParser *p, const char *tag, size_t taglen, const char *name,
	size_t namelen, const char *value, size_t valuelen)
{
	char buf[16];
	int n;

	n = xml_entitytostr(value, buf, sizeof(buf));
	if (n > 0)
		xmlattr(p, tag, taglen, name, namelen, buf, (size_t)n);
	else
		xmlattr(p, tag, taglen, name, namelen, value, valuelen);
}

static void
xmlattrend(XMLParser *p, const char *t, size_t tl, const char *n,
	size_t nl)
{
	struct node *cur;

	cur = &nodes[curnode];

	/* set base URL, if it is set it cannot be overwritten again */
	if (!basehrefset && basehrefdoc[0] &&
	    !attrcmp(n, "href") && !tagcmp(t, "base"))
		basehrefset = uri_parse(basehrefdoc, &base) != -1 ? 1 : 0;

	/* if attribute checked is set but it has no value then set it to "checked" */
	if (cur->tag.displaytype & DisplayInput && !attrcmp(n, "checked") && !attr_checked.len)
		string_append(&attr_checked, "checked", sizeof("checked") - 1);
}

static void
xmlattrstart(XMLParser *p, const char *t, size_t tl, const char *n,
	size_t nl)
{
	if (!attrcmp(n, "alt"))
		string_clear(&attr_alt);
	else if (!attrcmp(n, "checked"))
		string_clear(&attr_checked);
	else if (!attrcmp(n, "class"))
		string_clear(&attr_class);
	else if (!attrcmp(n, "data"))
		string_clear(&attr_data);
	else if (!attrcmp(n, "href"))
		string_clear(&attr_href);
	else if (!attrcmp(n, "id"))
		string_clear(&attr_id);
	else if (!attrcmp(n, "src"))
		string_clear(&attr_src);
	else if (!attrcmp(n, "type"))
		string_clear(&attr_type);
	else if (!attrcmp(n, "value"))
		string_clear(&attr_value);

	if (basehrefdoc[0] && !attrcmp(n, "href") && !tagcmp(t, "base"))
		basehrefdoc[0] = '\0';
}

void
usage(void)
{
	fprintf(stderr, "%s [-8adiIlrx] [-b basehref] [-s selector] [-u selector] [-w termwidth]\n", argv0);
	exit(1);
}

int
main(int argc, char **argv)
{
	if (pledge("stdio", NULL) < 0)
		err(1, "pledge");

	ARGBEGIN {
	case '8':
		str_bullet_item = "\xe2\x80\xa2 ";
		str_ruler = "\xe2\x94\x80"; /* symbol: "light horizontal" */
		break;
	case 'a':
		allowansi = !allowansi;
		break;
	case 'b':
		basehref = EARGF(usage());
		if (uri_parse(basehref, &base) == -1)
			usage();
		basehrefset = 1;
		break;
	case 'd':
		uniqrefs = !uniqrefs;
		break;
	case 'i':
		showrefinline = !showrefinline;
		break;
	case 'I':
		showurlinline = !showurlinline;
		break;
	case 'l':
		showrefbottom = !showrefbottom;
		break;
	case 'r':
		linewrap = !linewrap;
		break;
	case 's':
		sel_show = compileselectors(EARGF(usage()));
		/* switch to reader/selector mode, ignore all data except when matched */
		reader_mode = 1;
		reader_ignore = 1;
		break;
	case 'u':
		sel_hide = compileselectors(EARGF(usage()));
		/* switch to reader/selector mode */
		reader_mode = 1;
		break;
	case 'w':
		if ((termwidth = strtol(EARGF(usage()), NULL, 10)) < 1)
			usage();
		break;
	case 'x':
		resources = !resources;
		break;
	default:
		usage();
	} ARGEND

	/* top-most document root needs initialization */
	nodes[0].tag.name = "";

	parser.xmlattrstart = xmlattrstart;
	parser.xmlattr = xmlattr;
	parser.xmlattrentity = xmlattrentity;
	parser.xmlattrend = xmlattrend;
	parser.xmlcdatastart = xmlcdatastart;
	parser.xmlcdata = xmlcdata;
	parser.xmlcdataend = xmlcdataend;
	parser.xmldatastart = xmldatastart;
	parser.xmldata = xmldata;
	parser.xmldataentity = xmldataentity;
	parser.xmldataend = xmldataend;
	parser.xmltagstart = xmltagstart;
	parser.xmltagstartparsed = xmltagstartparsed;
	parser.xmltagend = xmltagend;

	parser.getnext = getchar;
	xml_parse(&parser);

	hflush();
	if (ncells > 0)
		newline();

	if (showrefbottom || resources)
		printlinkrefs();

	hflush();
	setmarkup(0);

	return 0;
}
