/*	$OpenBSD: tree.h,v 1.31 2023/03/08 04:43:09 guenther Exp $	*/
/*
 * Copyright 2002 Niels Provos <provos@citi.umich.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef	TREE_H
#define	TREE_H

/*
 * This file defines a red-black tree structure.
 *
 * A red-black tree is a binary search tree with the node color as an
 * extra attribute.  It fulfills a set of conditions:
 *	- every search path from the root to a leaf consists of the
 *	  same number of black nodes,
 *	- each red node (except for the root) has a black parent,
 *	- each leaf node is black.
 *
 * Every operation on a red-black tree is bounded as O(lg n).
 * The maximum height of a red-black tree is 2lg (n+1).
 */

/* Macros that define a red-black tree */
#define RB_HEAD(name, type)						\
struct name {								\
	struct type *rbh_root; /* root of the tree */			\
}

#define RB_INITIALIZER(root)						\
	{ NULL }

#define RB_INIT(root) do {						\
	(root)->rbh_root = NULL;					\
} while (0)

#define RB_BLACK	0
#define RB_RED		1
#define RB_ENTRY(type)							\
struct {								\
	struct type *rbe_left;		/* left element */		\
	struct type *rbe_right;		/* right element */		\
	struct type *rbe_parent;	/* parent element */		\
	int rbe_color;			/* node color */		\
}

#define RB_LEFT(elm, field)		(elm)->field.rbe_left
#define RB_RIGHT(elm, field)		(elm)->field.rbe_right
#define RB_PARENT(elm, field)		(elm)->field.rbe_parent
#define RB_COLOR(elm, field)		(elm)->field.rbe_color
#define RB_ROOT(head)			(head)->rbh_root
#define RB_EMPTY(head)			(RB_ROOT(head) == NULL)

#define RB_SET(elm, parent, field) do {					\
	RB_PARENT(elm, field) = parent;					\
	RB_LEFT(elm, field) = RB_RIGHT(elm, field) = NULL;		\
	RB_COLOR(elm, field) = RB_RED;					\
} while (0)

#define RB_SET_BLACKRED(black, red, field) do {				\
	RB_COLOR(black, field) = RB_BLACK;				\
	RB_COLOR(red, field) = RB_RED;					\
} while (0)

#define RB_ROTATE_LEFT(head, elm, tmp, field) do {			\
	(tmp) = RB_RIGHT(elm, field);					\
	if ((RB_RIGHT(elm, field) = RB_LEFT(tmp, field))) {		\
		RB_PARENT(RB_LEFT(tmp, field), field) = (elm);		\
	}								\
	if ((RB_PARENT(tmp, field) = RB_PARENT(elm, field))) {		\
		if ((elm) == RB_LEFT(RB_PARENT(elm, field), field))	\
			RB_LEFT(RB_PARENT(elm, field), field) = (tmp);	\
		else							\
			RB_RIGHT(RB_PARENT(elm, field), field) = (tmp);	\
	} else								\
		(head)->rbh_root = (tmp);				\
	RB_LEFT(tmp, field) = (elm);					\
	RB_PARENT(elm, field) = (tmp);					\
} while (0)

#define RB_ROTATE_RIGHT(head, elm, tmp, field) do {			\
	(tmp) = RB_LEFT(elm, field);					\
	if ((RB_LEFT(elm, field) = RB_RIGHT(tmp, field))) {		\
		RB_PARENT(RB_RIGHT(tmp, field), field) = (elm);		\
	}								\
	if ((RB_PARENT(tmp, field) = RB_PARENT(elm, field))) {		\
		if ((elm) == RB_LEFT(RB_PARENT(elm, field), field))	\
			RB_LEFT(RB_PARENT(elm, field), field) = (tmp);	\
		else							\
			RB_RIGHT(RB_PARENT(elm, field), field) = (tmp);	\
	} else								\
		(head)->rbh_root = (tmp);				\
	RB_RIGHT(tmp, field) = (elm);					\
	RB_PARENT(elm, field) = (tmp);					\
} while (0)

/* Moves node close to the key of elm to top
 */
#define	RB_GENERATE(name, type, field, cmp)				\
	RB_GENERATE_INTERNAL(name, type, field, cmp,)
#define RB_GENERATE_INTERNAL(name, type, field, cmp, attr)		\
attr void								\
name##_RB_INSERT_COLOR(struct name *head, struct type *elm)		\
{									\
	struct type *parent, *gparent, *tmp;				\
	while ((parent = RB_PARENT(elm, field)) &&			\
	    RB_COLOR(parent, field) == RB_RED) {			\
		gparent = RB_PARENT(parent, field);			\
		if (parent == RB_LEFT(gparent, field)) {		\
			tmp = RB_RIGHT(gparent, field);			\
			if (tmp && RB_COLOR(tmp, field) == RB_RED) {	\
				RB_COLOR(tmp, field) = RB_BLACK;	\
				RB_SET_BLACKRED(parent, gparent, field);\
				elm = gparent;				\
				continue;				\
			}						\
			if (RB_RIGHT(parent, field) == elm) {		\
				RB_ROTATE_LEFT(head, parent, tmp, field);\
				tmp = parent;				\
				parent = elm;				\
				elm = tmp;				\
			}						\
			RB_SET_BLACKRED(parent, gparent, field);	\
			RB_ROTATE_RIGHT(head, gparent, tmp, field);	\
		} else {						\
			tmp = RB_LEFT(gparent, field);			\
			if (tmp && RB_COLOR(tmp, field) == RB_RED) {	\
				RB_COLOR(tmp, field) = RB_BLACK;	\
				RB_SET_BLACKRED(parent, gparent, field);\
				elm = gparent;				\
				continue;				\
			}						\
			if (RB_LEFT(parent, field) == elm) {		\
				RB_ROTATE_RIGHT(head, parent, tmp, field);\
				tmp = parent;				\
				parent = elm;				\
				elm = tmp;				\
			}						\
			RB_SET_BLACKRED(parent, gparent, field);	\
			RB_ROTATE_LEFT(head, gparent, tmp, field);	\
		}							\
	}								\
	RB_COLOR(head->rbh_root, field) = RB_BLACK;			\
}									\
									\
/* Inserts a node into the RB tree */					\
attr struct type *							\
name##_RB_INSERT(struct name *head, struct type *elm)			\
{									\
	struct type *tmp;						\
	struct type *parent = NULL;					\
	int comp = 0;							\
	tmp = RB_ROOT(head);						\
	while (tmp) {							\
		parent = tmp;						\
		comp = (cmp)(elm, parent);				\
		if (comp < 0)						\
			tmp = RB_LEFT(tmp, field);			\
		else if (comp > 0)					\
			tmp = RB_RIGHT(tmp, field);			\
		else							\
			return (tmp);					\
	}								\
	RB_SET(elm, parent, field);					\
	if (parent != NULL) {						\
		if (comp < 0)						\
			RB_LEFT(parent, field) = elm;			\
		else							\
			RB_RIGHT(parent, field) = elm;			\
	} else								\
		RB_ROOT(head) = elm;					\
	name##_RB_INSERT_COLOR(head, elm);				\
	return (NULL);							\
}									\
									\
/* Finds the node with the same key as elm */				\
attr struct type *							\
name##_RB_FIND(struct name *head, struct type *elm)			\
{									\
	struct type *tmp = RB_ROOT(head);				\
	int comp;							\
	while (tmp) {							\
		comp = cmp(elm, tmp);					\
		if (comp < 0)						\
			tmp = RB_LEFT(tmp, field);			\
		else if (comp > 0)					\
			tmp = RB_RIGHT(tmp, field);			\
		else							\
			return (tmp);					\
	}								\
	return (NULL);							\
}

#define RB_INSERT(name, x, y)	name##_RB_INSERT(x, y)
#define RB_FIND(name, x, y)	name##_RB_FIND(x, y)

#endif	/* TREE_H */
