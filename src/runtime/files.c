#line 20 "files.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "spaces.h"
#include "trail.h"
#include "eval.h"
#include "cstring.h"
#include "cam.h"
#include "io_monad.h"
#include "trace.h"

#line 53 "files.nw"
#define FILE_TAG  ABSTRACT_TAG

enum file_flags {
    readable,
    writable
};

#define mask(flag)			(1<<(flag))
#define set_flag(flags,flag)		(flags |= mask(flag))
#define clear_flag(flags,flag)		(flags &= ~mask(flag))
#define test_flag(flags,flag)		(flags & mask(flag))

#define file_node_size wordsof(struct file_node)
struct file_node {
    NodeInfo *info;
    FILE     *fp;
    short    flags;
    short    bmode;
    long     bsize;
    char     *buffer;
};

static void finalize_file(Node *node);
static void close_handle(struct file_node *file);
static void close_readHandle(struct file_node *file);
static void close_writeHandle(struct file_node *file);

static NodeInfo file_info = {
    FILE_TAG, file_node_size, ot_binary, (Label)eval_whnf, "<<IO.Handle>>",
    finalize_file
};

static void
finalize_file(Node *file)
{
    close_handle((struct file_node *)file);
}

static void
close_handle(struct file_node *file)
{
    if ( file->fp != (FILE *)0 )
    {
	fclose(file->fp);
	file->fp    = (FILE *)0;
	file->flags = 0;
	if ( file->buffer != (char *)0 )
	    free(file->buffer);
    }
}

static void
close_readHandle(struct file_node *file)
{
    if ( file->flags & mask(writable) )
	file->flags &= ~mask(readable);
    else
	close_handle(file);
}

static void
close_writeHandle(struct file_node *file)
{
    if ( file->flags & mask(readable) )
	file->flags &= ~mask(writable);
    else
	close_handle(file);
}

#line 136 "files.nw"
static struct file_node stdin_node = {
    &file_info, (FILE *)0, mask(readable), -1, 0, (char *)0
};
static struct file_node stdout_node = {
    &file_info, (FILE *)0, mask(writable), -1, 0, (char *)0
};
static struct file_node stderr_node = {
    &file_info, (FILE *)0, mask(writable), _IONBF, 0, (char *)0
};


DECLARE_ENTRYPOINT(__stdin);
DECLARE_ENTRYPOINT(__stdout);
DECLARE_ENTRYPOINT(__stderr);

FUNCTION(__stdin)
{
    EXPORT_LABEL(__stdin)
 ENTRY_LABEL(__stdin)
    RETURN((Node *)&stdin_node);
}

FUNCTION(__stdout)
{
    EXPORT_LABEL(__stdout)
 ENTRY_LABEL(__stdout)
    RETURN((Node *)&stdout_node);
}

FUNCTION(__stderr)
{
    EXPORT_LABEL(__stderr)
 ENTRY_LABEL(__stderr)
    RETURN((Node *)&stderr_node);
}

#line 187 "files.nw"
enum {
    ReadMode_tag,
    WriteMode_tag,
    AppendMode_tag,
    ReadWriteMode_tag
};

DECLARE_CONST(__IO__ReadMode);
DECLARE_CONST(__IO__WriteMode);
DECLARE_CONST(__IO__AppendMode);
DECLARE_CONST(__IO__ReadWriteMode);

#define IO_ReadMode	 (Node *)&__IO__ReadMode_node
#define IO_WriteMode	 (Node *)&__IO__WriteMode_node
#define IO_AppendMode	 (Node *)&__IO__AppendMode_node
#define IO_ReadWriteMode (Node *)&__IO__ReadWriteMode_node

DECLARE_ENTRYPOINT(__openFile);
DECLARE_LABEL(__openFile_1);
DECLARE_LABEL(__openFile_2);


FUNCTION(__openFile)
{
    EXPORT_LABEL(__openFile)
 ENTRY_LABEL(__openFile)
    TRACE(("%I enter openFile%V\n", 3, sp));
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__openFile_1;
    GOTO(nf_string);
}

static
FUNCTION(__openFile_1)
{
    Node *fn;
    EXPORT_LABEL(__openFile_1)
 ENTRY_LABEL(__openFile_1)
    fn	  = sp[0];
    sp[0] = sp[1];
    sp[1] = fn;
    GOTO(__openFile_2);
}

static
FUNCTION(__openFile_2)
{
    const char	     *fn, *mode;
    int		     flags;
    FILE	     *fp;
    struct file_node *file;

 ENTRY_LABEL(__openFile_2)
    /* determine the access mode */
    EVAL_RIGID(__openFile_2);
    switch ( node_tag(sp[0]) )
    {
    case ReadMode_tag:
	mode  = "r";
	flags = mask(readable);
	break;
    case WriteMode_tag:
	mode  = "w";
	flags = mask(writable);
	break;
    case AppendMode_tag:
	mode  = "a";
	flags = mask(writable);
	break;
    case ReadWriteMode_tag:
	mode  = "r+";
	flags = mask(readable) | mask(writable);
	break;
    default:
	fprintf(stderr, "openFile: invalid mode\n");
	exit(2);
    }

    /* open the file */
    fn = to_string(sp[1]);
    fp = fopen(fn, mode);
    free((char *)fn);
    if ( fp == (FILE *)0 )
    {
	*++sp = from_string(strerror(errno));
	GOTO(__ioError);
    }
    else
	sp += 3;

    /* create the file node */
    CHECK_HEAP(file_node_size);
    file	 = (struct file_node *)hp;
    file->info	 = &file_info;
    file->fp	 = fp;
    file->flags  = flags;
    file->bmode  = -1;
    file->bsize  = 0;
    file->buffer = (char *)0;
    hp		+= file_node_size;
    register_final((Node *)file);

    /* return the file */
    RETURN((Node *)file);
}

#line 300 "files.nw"
DECLARE_ENTRYPOINT(__hClose);

FUNCTION(__hClose)
{
    struct file_node *file;

    EXPORT_LABEL(__hClose)
 ENTRY_LABEL(__hClose)
    EVAL_RIGID(__hClose);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    close_handle(file);

    sp += 2;
    RETURN(unit);
}

#line 324 "files.nw"
DECLARE_CONST(__prelude__False);
DECLARE_CONST(__prelude__True);

#define prelude_False (Node *)&__prelude__False_node
#define prelude_True  (Node *)&__prelude__True_node

DECLARE_ENTRYPOINT(__hIsOpen);
DECLARE_ENTRYPOINT(__hIsClosed);
DECLARE_ENTRYPOINT(__hIsReadable);
DECLARE_ENTRYPOINT(__hIsWritable);
DECLARE_ENTRYPOINT(__hIsSeekable);

FUNCTION(__hIsOpen)
{
    struct file_node *file;
    Node	     *r;

    EXPORT_LABEL(__hIsOpen)
 ENTRY_LABEL(__hIsOpen)
    EVAL_RIGID(__hIsOpen);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    sp += 2;

    r = file->flags & (mask(readable) | mask(writable))
	? prelude_True : prelude_False;
    RETURN(r);
}

FUNCTION(__hIsClosed)
{
    struct file_node *file;
    Node	     *r;

    EXPORT_LABEL(__hIsClosed)
 ENTRY_LABEL(__hIsClosed)
    EVAL_RIGID(__hIsClosed);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    sp += 2;

    r = file->fp == (FILE *)0 ? prelude_True : prelude_False;
    RETURN(r);
}

FUNCTION(__hIsReadable)
{
    struct file_node *file;
    Node	     *r;

    EXPORT_LABEL(__hIsReadable)
 ENTRY_LABEL(__hIsReadable)
    EVAL_RIGID(__hIsReadable);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    sp += 2;

    r = file->flags & mask(readable) ? prelude_True : prelude_False;
    RETURN(r);
}

FUNCTION(__hIsWritable)
{
    struct file_node *file;
    Node	     *r;

    EXPORT_LABEL(__hIsWritable)
 ENTRY_LABEL(__hIsWritable)
    EVAL_RIGID(__hIsWritable);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    sp += 2;

    r = file->flags & mask(writable) ? prelude_True : prelude_False;
    RETURN(r);
}

FUNCTION(__hIsSeekable)
{
    struct file_node *file;
    Node	     *r;

    EXPORT_LABEL(__hIsSeekable)
 ENTRY_LABEL(__hIsSeekable)
    EVAL_RIGID(__hIsSeekable);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    sp += 2;

    if ( !(file->flags & (mask(readable) | mask(writable))) )
	r = prelude_False;
    else if ( ftell(file->fp) != - 1 )
	r = prelude_True;
    else
    {
	clearerr(file->fp);
	r = prelude_False;
    }
    RETURN(r);
}

#line 440 "files.nw"
DECLARE_ENTRYPOINT(__isEOF);
DECLARE_ENTRYPOINT(__hIsEOF);

FUNCTION(__isEOF)
{
    EXPORT_LABEL(__isEOF)
 ENTRY_LABEL(__isEOF)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = (Node *)&stdin_node;
    GOTO(__hIsEOF);
}

FUNCTION(__hIsEOF)
{
    int		     c;
    Node	     *r;
    struct file_node *file;

    EXPORT_LABEL(__hIsEOF)
 ENTRY_LABEL(__hIsEOF)
    EVAL_RIGID(__hIsEOF);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(readable)) )
    {
	sp[0] = from_string("hIsEOF: handle not readable");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    c = getc(file->fp);
    if ( c == EOF && ferror(file->fp) )
    {
	int err = errno;

	close_readHandle(file);
	sp[0] = from_string(strerror(err));
	GOTO(__ioError);
    }
    ungetc(c, file->fp);

    sp += 2;
    r	= c == EOF ? prelude_True : prelude_False;
    RETURN(r);
}

#line 498 "files.nw"
DECLARE_ENTRYPOINT(__getChar);
DECLARE_ENTRYPOINT(__hGetChar);

FUNCTION(__getChar)
{
    EXPORT_LABEL(__getChar)
 ENTRY_LABEL(__getChar)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = (Node *)&stdin_node;
    GOTO(__hGetChar);
}

FUNCTION(__hGetChar)
{
    int		     c;
    Node	     *r;
    struct file_node *file;

    EXPORT_LABEL(__hGetChar)
 ENTRY_LABEL(__hGetChar)
    EVAL_RIGID(__hGetChar);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(readable)) )
    {
	sp[0] = from_string("hGetChar: handle not readable");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    c = getc(file->fp);
    if ( c == EOF )
    {
	boolean eof = feof(file->fp);
	int	err = errno;

	close_readHandle(file);
	sp[0] = from_string(eof ? "End of file" : strerror(err));
	GOTO(__ioError);
    }

    sp += 2;
    r	= (Node *)(char_table + (c & 0xff));
    RETURN(r);
}

#line 551 "files.nw"
DECLARE_ENTRYPOINT(__hLookAhead);

FUNCTION(__hLookAhead)
{
    int		     c;
    Node	     *r;
    struct file_node *file;

    EXPORT_LABEL(__hLookAhead)
 ENTRY_LABEL(__hLookAhead)
    EVAL_RIGID(__hLookAhead);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(readable)) )
    {
	sp[0] = from_string("hLookAhead: handle not readable");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    c = getc(file->fp);
    if ( c == EOF )
    {
	boolean eof = feof(file->fp);
	int	err = errno;

	if ( !eof )
	    close_readHandle(file);
	sp[0] = from_string(eof ? "End of file" : strerror(err));
	GOTO(__ioError);
    }
    ungetc(c, file->fp);

    sp += 2;
    r	= (Node *)(char_table + (c & 0xff));
    RETURN(r);
}

#line 612 "files.nw"
DECLARE_ENTRYPOINT(__getLine);
DECLARE_ENTRYPOINT(__hGetLine);

FUNCTION(__getLine)
{
    EXPORT_LABEL(__getLine)
 ENTRY_LABEL(__getLine)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = (Node *)&stdin_node;
    GOTO(__hGetLine);
}

FUNCTION(__hGetLine)
{
    char buf[256], *cp;
    Node *line, *tail;
    FILE *fp;

    EXPORT_LABEL(__hGetLine)
 ENTRY_LABEL(__hGetLine)
    EVAL_RIGID(__hGetLine);
    ASSERT(is_boxed(sp[0]) && node_tag(sp[0]) == FILE_TAG);

    if ( !(((struct file_node *)sp[0])->flags & mask(readable)) )
    {
	sp[0] = from_string("hGetLine: handle not readable");
	GOTO(__ioError);
    }

    fp = ((struct file_node *)sp[0])->fp;
    ASSERT(fp != (FILE *)0);
    if ( fgets(buf, 256, fp) == (char *)0 )
    {
	boolean eof = feof(fp);
	int	err = errno;

	close_readHandle((struct file_node *)sp[0]);
	sp[0] = from_string(eof ? "End of file" : strerror(err));
	GOTO(__ioError);
    }

    CHECK_STACK(2);
    sp   -= 2;
    sp[0] = sp[1] = (Node *)0;
    sp[3] = nil;

    do
    {
	for ( cp = buf; *cp != '\n' && *cp != '\0'; cp++ )
	    ;

	if ( *cp == '\n' )
	{
	    *cp  = '\0';
	    tail = nil;
	}
	else
	{
	    CHECK_HEAP(indir_node_size);
	    tail	 = (Node *)hp;
	    tail->n.info = &indir_info;
	    tail->n.node = nil;
	    hp		+= indir_node_size;
	}

	sp[0] = tail;
	line  = prefix_string(buf, tail);
	if ( sp[3] == nil )
	    sp[3] = line;
	else
	    sp[1]->n.node = line;
	sp[1] = sp[0];
    } while ( sp[1] != nil && fgets(buf, 256, fp) != (char *)0 );

    if ( sp[1] != nil )
	close_readHandle((struct file_node *)sp[2]);

    line = sp[3];
    sp	+= 4;
    RETURN(line);
}

#line 708 "files.nw"
DECLARE_ENTRYPOINT(__readFile);
DECLARE_ENTRYPOINT(__getContents);
DECLARE_ENTRYPOINT(__hGetContents);
DECLARE_LABEL(lazyRead);
DECLARE_LABEL(lazyRead_eval);
DECLARE_LABEL(lazyRead_lazy);

static FunctionInfo lazyRead_info	  = FUNINFO("lazyRead", lazyRead, 2);
static NodeInfo     lazyRead_suspend_info = SUSPINFO(lazyRead);

FUNCTION(__readFile)
{
    Node *fn, *world;

    EXPORT_LABEL(__readFile)
 ENTRY_LABEL(__readFile)
    fn	  = sp[0];
    world = sp[1];

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = fn;
    sp[1] = IO_ReadMode;
    sp[2] = world;
    sp[3] = (Node *)__hGetContents;
    GOTO(__openFile);
}

FUNCTION(__getContents)
{
    EXPORT_LABEL(__getContents)
 ENTRY_LABEL(__getContents)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = (Node *)&stdin_node;
    GOTO(__hGetContents);
}

FUNCTION(__hGetContents)
{
    Node		*clos, *susp;
    struct file_node	*file;

    EXPORT_LABEL(__hGetContents)
 ENTRY_LABEL(__hGetContents)
    EVAL_RIGID(__hGetContents);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(readable)) )
    {
	sp[0] = from_string("hGetContents: handle not readable");
	GOTO(__ioError);
    }

    /* put the file into a semi-closed state */
    file->flags &= ~mask(readable);

    /* construct the (lazy) input stream */
    CHECK_HEAP(closure_node_size(2) + suspend_node_size);
    clos	     = (Node *)hp;
    clos->cl.info    = &lazyRead_info;
    clos->cl.args[0] = (Node *)hp;
    clos->cl.args[1] = sp[0];
    hp		    += closure_node_size(2);

    susp	 = (Node *)hp;
    susp->s.info = &lazyRead_suspend_info;
    susp->s.fn	 = clos;
    susp->s.spc	 = (SearchSpace *)0;
    hp	        += suspend_node_size;

    sp += 2;
    RETURN(susp);
}

static
FUNCTION(lazyRead_eval)
{
    Node *clos;
 ENTRY_LABEL(lazyRead_eval)
    CHECK_STACK1();
    clos  = sp[0];
    sp	 -= 1;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    GOTO(lazyRead);
}

static
FUNCTION(lazyRead_lazy)
{
    Node *susp, *clos;
 ENTRY_LABEL(lazyRead_lazy)
    susp = sp[0];

    /* suspend the search if the node is not local */
    if ( !is_local_space(susp->s.spc) )
	GOTO(suspend_thread(resume, susp));

    /* lock the suspension */
    clos = susp->s.fn;
    SAVE(susp, q.wq);
    susp->info = &queueMe_info;
    susp->q.wq = (ThreadQueue)0;

    /* create an update frame */
    CHECK_STACK(3);
    sp   -= 3;
    sp[0] = clos->cl.args[0];
    sp[1] = clos->cl.args[1];
    sp[2] = (Node *)update;

    /* enter the callee */
    GOTO(lazyRead);
}

static
FUNCTION(lazyRead)
{
    int		     c;
    Node	     *list, *tail;
    struct file_node *file;

 ENTRY_LABEL(lazyRead)
    file = (struct file_node *)sp[1];
    if ( file->fp == (FILE *)0 )
	list = nil;
    else
    {
	c = fgetc(file->fp);
	if ( c == EOF )
	{
	    close_readHandle(file);
	    list = nil;
	}
	else
	{
	    CHECK_HEAP(suspend_node_size + cons_node_size);

	    tail	 = (Node *)hp;
	    tail->s.info = &lazyRead_suspend_info;
	    tail->s.fn   = sp[0];
	    tail->s.spc  = (SearchSpace *)0;
	    hp		+= suspend_node_size;

	    list	    = (Node *)hp;
	    list->c.info    = &cons_info;
	    list->c.args[0] = (Node *)(char_table + (c & 0xff));
	    list->c.args[1] = tail;
	    hp		   += cons_node_size;
	}
    }

    sp += 2;
    RETURN(list);
}

#line 872 "files.nw"
DECLARE_ENTRYPOINT(__putChar);
DECLARE_ENTRYPOINT(__hPutChar);
DECLARE_LABEL(__hPutChar_1);

FUNCTION(__putChar)
{
    EXPORT_LABEL(__putChar)
 ENTRY_LABEL(__putChar)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)&stdout_node;
    GOTO(__hPutChar_1);
}

FUNCTION(__hPutChar)
{
    Node *file;

    EXPORT_LABEL(__hPutChar)
 ENTRY_LABEL(__hPutChar)
    EVAL_RIGID(__hPutChar);
    file  = sp[0];
    sp[0] = sp[1];
    sp[1] = file;
    GOTO(__hPutChar_1);
}

static
FUNCTION(__hPutChar_1)
{
    struct file_node *file;
 ENTRY_LABEL(__hPutChar_1)
    EVAL_RIGID_CHAR(__hPutChar_1);

    file = (struct file_node *)sp[1];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(writable)) )
    {
	*++sp = from_string("hPutChar: handle not writable");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    if ( putc(sp[0]->ch.ch, file->fp) == EOF )
    {
	int err = errno;

	close_writeHandle(file);
	*++sp = from_string(strerror(err));
	GOTO(__ioError);
    }

    sp += 3;
    RETURN(unit);
}

#line 935 "files.nw"
DECLARE_ENTRYPOINT(__putStr);
DECLARE_ENTRYPOINT(__hPutStr);
DECLARE_LABEL(__hPutStr_1);
DECLARE_LABEL(__hPutStr_2);

FUNCTION(__putStr)
{
    EXPORT_LABEL(__putStr)
 ENTRY_LABEL(__putStr)
    CHECK_STACK(1);
    sp	 -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)&stdout_node;
    GOTO(__hPutStr_1);
}

FUNCTION(__hPutStr)
{
    Node *file;

    EXPORT_LABEL(__hPutStr)
 ENTRY_LABEL(__hPutStr)
    EVAL_RIGID(__hPutStr);
    file = sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(((struct file_node *)file)->flags & mask(writable)) )
    {
	*++sp = from_string("hPutStr: handle not writable");
	GOTO(__ioError);
    }

    sp[0] = sp[1];
    sp[1] = file;
    GOTO(__hPutStr_1);
}

static
FUNCTION(__hPutStr_1)
{
    Node *list;
 ENTRY_LABEL(__hPutStr_1)
    EVAL_RIGID(__hPutStr_1);
    list = sp[0];
    switch ( node_tag(list) )
    {
    case NIL_TAG:
	sp += 3;
	RETURN(unit);
    case CONS_TAG:
	CHECK_STACK1();
	sp   -= 1;
	sp[0] = list->c.args[0];
	sp[1] = list->c.args[1];
	GOTO(__hPutStr_2);
    default:
	break;
    }
    fprintf(stderr, "hPutStr: invalid argument\n");
    exit(2);
}

static
FUNCTION(__hPutStr_2)
{
    struct file_node *file;
 ENTRY_LABEL(__hPutStr_2)
    EVAL_RIGID_CHAR(__hPutStr_2);

    file = (struct file_node *)sp[2];
    if ( fputc(sp[0]->ch.ch, file->fp) == EOF )
    {
	int err = errno;

	close_writeHandle(file);
	sp   += 2;
	sp[0] = from_string(strerror(err));
	GOTO(__ioError);
    }

    sp += 1;
    GOTO(__hPutStr_1);
}

#line 1030 "files.nw"
DECLARE_ENTRYPOINT(__writeFile);
DECLARE_ENTRYPOINT(__appendFile);
DECLARE_ENTRYPOINT(__hPutContents);
DECLARE_LABEL(__hPutContents_1);

FUNCTION(__writeFile)
{
    Node *fn, *world;

    EXPORT_LABEL(__writeFile)
 ENTRY_LABEL(__writeFile)
    fn	  = sp[0];
    world = sp[2];

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = fn;
    sp[1] = IO_WriteMode;
    sp[2] = world;
    sp[3] = (Node *)__hPutContents;
    GOTO(__openFile);
}

FUNCTION(__appendFile)
{
    Node *fn, *world;

    EXPORT_LABEL(__appendFile)
 ENTRY_LABEL(__appendFile)
    fn	  = sp[0];
    world = sp[2];

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = fn;
    sp[1] = IO_AppendMode;
    sp[2] = world;
    sp[3] = (Node *)__hPutContents;
    GOTO(__openFile);
}

FUNCTION(__hPutContents)
{
    Node *file, *str, *world;

    EXPORT_LABEL(__hPutContents)
 ENTRY_LABEL(__hPutContents)
    file  = sp[0];
    str	  = sp[1];
    world = sp[2];

    CHECK_STACK(3);
    sp	 -= 3;
    sp[0] = file;
    sp[1] = str;
    sp[2] = world;
    sp[3] = (Node *)__hPutContents_1;
    sp[4] = file;
    GOTO(__hPutStr);
}

static
FUNCTION(__hPutContents_1)
{
 ENTRY_LABEL(__hPutContents_1)
    sp += 1;
    GOTO(__hClose);
}

#line 1104 "files.nw"
DECLARE_ENTRYPOINT(__hFileSize);

FUNCTION(__hFileSize)
{
    long	     curpos, endpos;
    Node	     *r;
    struct file_node *file;

    EXPORT_LABEL(__hFileSize)
 ENTRY_LABEL(__hFileSize)
    EVAL_RIGID(__hFileSize);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	sp[0] = from_string("hFileSize: handle not open");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    curpos = ftell(file->fp);
    if ( curpos == -1 || fseek(file->fp, 0, SEEK_END) == -1 )
    {
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }

    endpos = ftell(file->fp);
    if ( endpos == -1 || fseek(file->fp, curpos, SEEK_SET) == -1 )
    {
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }

    sp += 2;
#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = endpos;
    hp	   += int_node_size;
#else
    r = mk_int(endpos);
#endif
    RETURN(r);
}

#line 1158 "files.nw"
DECLARE_ENTRYPOINT(__hIsTerminalDevice);

FUNCTION(__hIsTerminalDevice)
{
    Node	     *r;
    struct file_node *file;

    EXPORT_LABEL(__hIsTerminalDevice)
 ENTRY_LABEL(__hIsTerminalDevice)
    EVAL_RIGID(__hIsTerminalDevice);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	sp[0] = from_string("hIsTerminalDevice: handle not open");
	GOTO(__ioError);
    }
    ASSERT(file->fp != (FILE *)0);

    sp += 2;
    r	= isatty(fileno(file->fp)) ? prelude_True : prelude_False;
    RETURN(r);
}

#line 1200 "files.nw"
enum { Nothing_tag, Just_tag };
DECLARE_CONST(__prelude__Nothing);
DECLARE_DATA(__prelude__Just);

enum { NoBuffering_tag, LineBuffering_tag, BlockBuffering_tag };
DECLARE_CONST(__IO__NoBuffering);
DECLARE_CONST(__IO__LineBuffering);
DECLARE_DATA(__IO__BlockBuffering);

DECLARE_ENTRYPOINT(__hGetBuffering); 

FUNCTION(__hGetBuffering)
{
    short	     bmode;
    long	     bsize;
    Node	     *size, *r;
    struct file_node *file;

    EXPORT_LABEL(__hGetBuffering)
 ENTRY_LABEL(__hGetBuffering)
    EVAL_RIGID(__hGetBuffering);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	sp[0] = from_string("hGetBuffering: handle not open");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    sp += 2;
    for (;;)
    {
	bmode = file->bmode;
	bsize = file->bsize;
	switch ( bmode )
	{
	case -1:
	    file->bmode = isatty(fileno(file->fp)) ? _IOLBF : _IOFBF;
	    continue;
	case _IONBF:
	    r = (Node *)&__IO__NoBuffering_node;
	    break;
	case _IOLBF:
	    r = (Node *)&__IO__LineBuffering_node;
	    break;
	case _IOFBF:
	    CHECK_HEAP(int_node_size + 2 * constr_node_size(1));
	    if ( bsize != 0 )
	    {
 #if ONLY_BOXED_OBJECTS
		r       = (Node *)hp;
		r->info = &int_info;
	        r->i.i  = bsize;
		hp     += int_node_size;
#else
		r = mk_int(bsize);
#endif
		size		= (Node *)hp;
		size->info	= &__prelude__Just_info;
		size->c.args[0] = r;
		hp	       += constr_node_size(1);
	    }
	    else
		size = (Node *)&__prelude__Nothing_node;

	    r		 = (Node *)hp;
	    r->info	 = &__IO__BlockBuffering_info;
	    r->c.args[0] = size;
	    hp		+= constr_node_size(1);
	    break;
	default:
	    fprintf(stderr, "hGetBuffering: invalid buffer mode %d\n", bmode);
	    exit(2);
	}
	break;
    }

    RETURN(r);
}

#line 1287 "files.nw"
DECLARE_ENTRYPOINT(__hSetBuffering);
DECLARE_LABEL(__hSetBuffering_1);
DECLARE_LABEL(__hSetBuffering_2);
DECLARE_LABEL(__hSetBuffering_3);

FUNCTION(__hSetBuffering)
{
    Node *file;
    EXPORT_LABEL(__hSetBuffering)
 ENTRY_LABEL(__hSetBuffering)
    EVAL_RIGID(__hSetBuffering);
    file  = sp[0];
    sp[0] = sp[1];
    sp[1] = file;
    GOTO(__hSetBuffering_1);
}

static
FUNCTION(__hSetBuffering_1)
{
    short	     bmode;
    struct file_node *file;
 ENTRY_LABEL(__hSetBuffering_1)
    EVAL_RIGID(__hSetBuffering_1);
    switch ( node_tag(sp[0]) )
    {
    case NoBuffering_tag:
	bmode = _IONBF;
	break;
    case LineBuffering_tag:
	bmode = _IOLBF;
	break;
    case BlockBuffering_tag:
	sp[0] = sp[0]->c.args[0];
	GOTO(__hSetBuffering_2);
    default:
	fprintf(stderr, "hSetBuffering: invalid mode\n");
	exit(2);
    }

    file = (struct file_node *)sp[1];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	*++sp = from_string("hSetBuffering: handle not open");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    if ( setvbuf(file->fp, (char *)0, bmode, 0) == -1 )
    {
	*++sp = from_string(strerror(errno));
	GOTO(__ioError);
    }
    file->bmode = bmode;
    file->bsize = 0;
    if ( file->buffer != (char *)0 )
	free(file->buffer);
    file->buffer = (char *)0;

    sp += 3;
    RETURN(unit);
}

static
FUNCTION(__hSetBuffering_2)
{
    struct file_node *file;
 ENTRY_LABEL(__hSetBuffering_2)
    EVAL_RIGID(__hSetBuffering_2);
    switch ( node_tag(sp[0]) )
    {
    case Nothing_tag:
	break;
    case Just_tag:
	sp[0] = sp[0]->c.args[0];
	GOTO(__hSetBuffering_3);
    default:
	fprintf(stderr, "hSetBuffering: invalid mode\n");
	exit(2);
    }

    file = (struct file_node *)sp[1];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	*++sp = from_string("hSetBuffering: handle not open");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    if ( setvbuf(file->fp, (char *)0, _IOFBF, 0) == -1 )
    {
	*++sp = from_string(strerror(errno));
	GOTO(__ioError);
    }
    file->bmode = _IOFBF;
    file->bsize = 0;
    if ( file->buffer != (char *)0 )
	free(file->buffer);
    file->buffer = (char *)0;

    sp += 3;
    RETURN(unit);
}

static
FUNCTION(__hSetBuffering_3)
{
    long	     bsize;
    char	     *buffer;
    struct file_node *file;
 ENTRY_LABEL(__hSetBuffering_3)
    EVAL_RIGID_INT(__hSetBuffering_3);
    file  = (struct file_node *)sp[1];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);
    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	*++sp = from_string("hSetBuffering: handle not open");
	GOTO(__ioError);
    }

    bsize = int_val(sp[0]);
    if ( bsize > 0 )
    {
	buffer = (char *)malloc(bsize);
	if ( buffer == (char *)0 )
	{
	    fprintf(stderr, "hSetBuffering: memory exhausted\n");
	    exit(1);
	}
    }
    else
	buffer = (char *)0;

    ASSERT(file->fp != (FILE *)0);
    if ( setvbuf(file->fp, buffer, _IOFBF, bsize) == -1 )
    {
	*++sp = from_string(strerror(errno));
	free(buffer);
	GOTO(__ioError);
    }
    file->bmode = _IOFBF;
    file->bsize = bsize;
    if ( file->buffer != (char *)0 )
	free(file->buffer);
    file->buffer = buffer;

    sp += 3;
    RETURN(unit);
}

#line 1444 "files.nw"
DECLARE_ENTRYPOINT(__hFlush);

FUNCTION(__hFlush)
{
    struct file_node *file;

    EXPORT_LABEL(__hFlush)
 ENTRY_LABEL(__hFlush)
    EVAL_RIGID(__hFlush);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & mask(writable)) )
    {
	sp[0] = from_string("hFlush: handle not writable");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    if ( fflush(file->fp) == -1 )
    {
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }

    sp += 2;
    RETURN(unit);
}

#line 1478 "files.nw"
DECLARE_ENTRYPOINT(__hTell); 

FUNCTION(__hTell)
{
    long	     curpos;
    Node	     *r;
    struct file_node *file;
    EXPORT_LABEL(__hTell)
 ENTRY_LABEL(__hTell)
    EVAL_RIGID(__hTell);
    file = (struct file_node *)sp[0];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	sp[0] = from_string("hTell: handle not open");
	GOTO(__ioError);
    }

    ASSERT(file->fp != (FILE *)0);
    curpos = ftell(file->fp);
    if ( curpos == -1 )
    {
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }

    sp += 2;
#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    r	    = (Node *)hp;
    r->info = &int_info;
    r->i.i  = curpos;
    hp	   += int_node_size;
#else
    r = mk_int(curpos);
#endif
    RETURN(r);
}

#line 1528 "files.nw"
enum { AbsoluteSeek_tag, RelativeSeek_tag, SeekFromEnd_tag };
DECLARE_CONST(__IO__AbsoluteSeek);
DECLARE_CONST(__IO__RelativeSeek);
DECLARE_CONST(__IO__SeekFromEnd);

DECLARE_ENTRYPOINT(__hSeek);
DECLARE_LABEL(__hSeek_1);
DECLARE_LABEL(__hSeek_2);

FUNCTION(__hSeek)
{
    Node *file;

    EXPORT_LABEL(__hSeek)
 ENTRY_LABEL(__hSeek)
    EVAL_RIGID(__hSeek);
    file  = sp[0];
    sp[0] = sp[1];
    sp[1] = file;
    GOTO(__hSeek_1);
}

static
FUNCTION(__hSeek_1)
{
    Node *mode;

 ENTRY_LABEL(__hSeek_1)
    EVAL_RIGID(__hSeek_1);
    mode  = sp[0];
    sp[0] = sp[2];
    sp[2] = mode;
    GOTO(__hSeek_2);
}

static
FUNCTION(__hSeek_2)
{
    int		     smode;
    struct file_node *file;
 ENTRY_LABEL(__hSeek_2)
    EVAL_RIGID_INT(__hSeek_2);

    file = (struct file_node *)sp[1];
    ASSERT(is_boxed(file) && node_tag(file) == FILE_TAG);

    if ( !(file->flags & (mask(readable) | mask(writable))) )
    {
	sp   += 2;
	sp[0] = from_string("hSeek: handle not open");
	GOTO(__ioError);
    }

    switch ( node_tag(sp[2]) )
    {
    case AbsoluteSeek_tag:
	smode = SEEK_SET;
	break;
    case RelativeSeek_tag:
	smode = SEEK_CUR;
	break;
    case SeekFromEnd_tag:
	smode = SEEK_END;
	break;
    default:
	fprintf(stderr, "hSeek: invalid mode\n");
	exit(2);
    }

    ASSERT(file->fp != (FILE *)0);
    if ( fseek(file->fp, int_val(sp[0]), smode) == -1 )
    {
	sp   += 2;
	sp[0] = from_string(strerror(errno));
	GOTO(__ioError);
    }

    sp += 4;
    RETURN(unit);
}

#line 1614 "files.nw"
void
init_files(int bmode, long bsize)
{
    char *buffer;

    /* set up the standard file pointers */
    stdin_node.fp = stdin;
    stdout_node.fp = stdout;
    stderr_node.fp = stderr;

    /* eventually change buffer modes for standard input and output */
    if ( bmode != -1 )
    {
	/* don't allocate buffers if the file is not fully buffered */
	if ( bmode != _IOFBF )
	    bsize = 0;

	/* change the buffer mode for the standard input channel */
	if ( bsize != 0 )
	{
	    buffer = (char *)malloc(bsize);
	    if ( buffer == (char *)0 )
	    {
		fprintf(stderr, "cannot not allocate input buffer\n");
		exit(1);
	    }
	}
	else
	    buffer = (char *)0;
	if ( setvbuf(stdin, buffer, bmode, bsize) == -1 )
	{
	    perror("setvbuf(stdin)");
	    exit(1);
	}
	stdin_node.bmode  = bmode;
	stdin_node.bsize  = bsize;
	stdin_node.buffer = buffer;

	/* change the buffer mode for the standard input channel */
	if ( bsize != 0 )
	{
	    buffer = (char *)malloc(bsize);
	    if ( buffer == (char *)0 )
	    {
		fprintf(stderr, "cannot not allocate output buffer\n");
		exit(1);
	    }
	}
	else
	    buffer = (char *)0;
	if ( setvbuf(stdout, buffer, bmode, bmode) == -1 )
	{
	    perror("setvbuf(stdout)");
	    exit(1);
	}
	stdout_node.bmode  = bmode;
	stdout_node.bsize  = bsize;
	stdout_node.buffer = buffer;
    }
}
