#line 12 "directory.nw"
#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <dirent.h>
#include "debug.h"
#include "run.h"
#include "heap.h"
#include "stack.h"
#include "threads.h"
#include "eval.h"
#include "cstring.h"
#include "io_monad.h"
#include "cam.h"
#include "trace.h"

#define prelude_True  (Node *)&__prelude__True_node
#define prelude_False (Node *)&__prelude__False_node

DECLARE_CONST(__prelude__True);
DECLARE_CONST(__prelude__False);

#line 45 "directory.nw"
DECLARE_ENTRYPOINT(__createDirectory);
DECLARE_ENTRYPOINT(__removeDirectory);

DECLARE_LABEL(__createDirectory_1);
DECLARE_LABEL(__removeDirectory_1);

FUNCTION(__createDirectory)
{
    EXPORT_LABEL(__createDirectory)
 ENTRY_LABEL(__createDirectory)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__createDirectory_1;
    GOTO(nf_string);
}

static
FUNCTION(__createDirectory_1)
{
    char *d;
 ENTRY_LABEL(__createDirectory_1)
    d = to_string(sp[0]);
    if ( mkdir(d, 0777) )
    {
        free(d);
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }
    free(d);
    sp += 2;
    RETURN(unit);
}

FUNCTION(__removeDirectory)
{
    EXPORT_LABEL(__removeDirectory)
 ENTRY_LABEL(__removeDirectory)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__removeDirectory_1;
    GOTO(nf_string);
}

static
FUNCTION(__removeDirectory_1)
{
    char *d;
 ENTRY_LABEL(__removeDirectory_1)
    d = to_string(sp[0]);
    if ( rmdir(d) )
    {
        free(d);
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }
    free(d);
    sp += 2;
    RETURN(unit);
}

#line 113 "directory.nw"
DECLARE_ENTRYPOINT(__removeFile);

DECLARE_LABEL(__removeFile_1);

FUNCTION(__removeFile)
{
    EXPORT_LABEL(__removeFile)
 ENTRY_LABEL(__removeFile)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__removeFile_1;
    GOTO(nf_string);
}

static
FUNCTION(__removeFile_1)
{
    char *f;
 ENTRY_LABEL(__removeFile_1)
    f = to_string(sp[0]);
    if ( unlink(f) )
    {
        free(f);
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }
    free(f);
    sp += 2;
    RETURN(unit);
}

#line 150 "directory.nw"
DECLARE_ENTRYPOINT(__renameDirectory);
DECLARE_ENTRYPOINT(__renameFile);

DECLARE_LABEL(__renameDirectory_1);
DECLARE_LABEL(__renameDirectory_2);
DECLARE_LABEL(__renameFile_1);
DECLARE_LABEL(__renameFile_2);

FUNCTION(__renameDirectory)
{
    EXPORT_LABEL(__renameDirectory)
 ENTRY_LABEL(__renameDirectory)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__renameDirectory_1;
    GOTO(nf_string);
}

static
FUNCTION(__renameDirectory_1)
{
    Node *from, *to;
 ENTRY_LABEL(__renameDirectory_1)
    CHECK_STACK1();
    from  = sp[0];
    to    = sp[1];
    sp   -= 1;
    sp[0] = to;
    sp[1] = (Node *)__renameDirectory_2;
    sp[2] = from;
    GOTO(nf_string);
}

static
FUNCTION(__renameDirectory_2)
{
    char        *from, *to;
    int         r;
    struct stat st;
 ENTRY_LABEL(__renameDirectory_2)
    from = to_string(sp[1]);
    to   = to_string(sp[0]);
    r    = stat(from, &st);
    if ( r == 0 )
    {
        if ( st.st_mode & S_IFDIR )
            r = rename(from, to);
        else
        {
            r     = -1;
            errno = ENOTDIR;
        }
    }
    free(from);
    free(to);
    if ( r )
    {
        *++sp = from_string(strerror(errno));
        GOTO(__ioError);
    }
    sp += 3;
    RETURN(unit);
}

FUNCTION(__renameFile)
{
    EXPORT_LABEL(__renameFile)
 ENTRY_LABEL(__renameFile)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__renameFile_1;
    GOTO(nf_string);
}

static
FUNCTION(__renameFile_1)
{
    Node *from, *to;
 ENTRY_LABEL(__renameFile_1)
    CHECK_STACK1();
    from  = sp[0];
    to    = sp[1];
    sp   -= 1;
    sp[0] = to;
    sp[1] = (Node *)__renameFile_2;
    sp[2] = from;
    GOTO(nf_string);
}

static
FUNCTION(__renameFile_2)
{
    char        *from, *to;
    int         r;
    struct stat st;
 ENTRY_LABEL(__renameFile_2)
    from = to_string(sp[1]);
    to   = to_string(sp[0]);
    r    = stat(from, &st);
    if ( r == 0 )
    {
        if ( !(st.st_mode & S_IFDIR) )
            r = rename(from, to);
        else
        {
            r     = -1;
            errno = EISDIR;
        }
    }
    free(from);
    free(to);
    if ( r )
    {
        *++sp = from_string(strerror(errno));
        GOTO(__ioError);
    }
    sp += 3;
    RETURN(unit);
}

#line 285 "directory.nw"
DECLARE_ENTRYPOINT(__getDirectoryContents);
DECLARE_LABEL(__getDirectoryContents_1);

FUNCTION(__getDirectoryContents)
{
    EXPORT_LABEL(__getDirectoryContents)
 ENTRY_LABEL(__getDirectoryContents)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__getDirectoryContents_1;
    GOTO(nf_string);
}

static
FUNCTION(__getDirectoryContents_1)
{
    char          *d;
    DIR           *dir;
    struct dirent *ent; 
    Node          *r, *cons;
 ENTRY_LABEL(__getDirectoryContents_1)

    d   = to_string(sp[0]);
    dir = opendir(d);
    free(d);
    if ( dir == (DIR *)0 )
    {
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }

    /* stack layout for the following loop:
     * sp[0]: the head of the list
     * sp[1]: the current tail node of the list (or NULL)
     * sp[2]: used for protecting the filename across a garbage collection
     */
    CHECK_STACK(1);
    sp   -= 1;
    sp[0] = sp[1] = sp[2] = (Node *)0;
    for ( ent = readdir(dir); ent != (struct dirent *)0; ent = readdir(dir) )
    {
        sp[2]           = from_string(ent->d_name);
        CHECK_HEAP(cons_node_size);
        cons            = (Node *)hp;
        cons->info      = &cons_info;
        cons->c.args[0] = sp[2];
        cons->c.args[1] = (Node *)0;
        hp             += cons_node_size;
        if ( sp[0] == (Node *)0 )
            sp[0] = cons;
        else
            sp[1]->c.args[1] = cons;
        sp[1] = cons;
    }
    closedir(dir);

    /* fix the tail of the list */
    if ( sp[0] == (Node *)0 )
        r = nil;
    else
    {
        sp[1]->c.args[1] = nil;
        r                = sp[0];
    }
    sp += 3;
    RETURN(r);
}

#line 359 "directory.nw"
DECLARE_ENTRYPOINT(__getCurrentDirectory);
DECLARE_ENTRYPOINT(__setCurrentDirectory);

DECLARE_LABEL(__setCurrentDirectory_1);

FUNCTION(__getCurrentDirectory)
{
    char *cwd;
    Node *r;
    EXPORT_LABEL(__getCurrentDirectory)
 ENTRY_LABEL(__getCurrentDirectory)

    cwd = (char *)malloc(MAXPATHLEN + 1);
    if ( cwd == (char *)0 )
    {
        fprintf(stderr, "getCurrentDirectory: memory exhausted\n");
        exit(1);
    }

    if ( getcwd(cwd, MAXPATHLEN) == (char *)0 )
    {
        CHECK_STACK1();
        r     = from_string(strerror(errno));
        *--sp = r;
        GOTO(__ioError);
    }

    sp += 1;
    r   = from_string(cwd);
    free(cwd);
    RETURN(r);
}

FUNCTION(__setCurrentDirectory)
{
    EXPORT_LABEL(__setCurrentDirectory)
 ENTRY_LABEL(__setCurrentDirectory)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__setCurrentDirectory_1;
    GOTO(nf_string);
}

static
FUNCTION(__setCurrentDirectory_1)
{
    char *cwd;
 ENTRY_LABEL(__setCurrentDirectory_1)
    cwd = to_string(sp[0]);
    if ( chdir(cwd) )
    {
        free(cwd);
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }
    free(cwd);
    sp += 2;
    RETURN(unit);
}


#line 428 "directory.nw"
DECLARE_ENTRYPOINT(__doesDirectoryExist);
DECLARE_ENTRYPOINT(__doesFileExist);

DECLARE_LABEL(__doesDirectoryExist_1);
DECLARE_LABEL(__doesFileExist_1);

FUNCTION(__doesDirectoryExist)
{
    EXPORT_LABEL(__doesDirectoryExist)
 ENTRY_LABEL(__doesDirectoryExist)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__doesDirectoryExist_1;
    GOTO(nf_string);
}

static
FUNCTION(__doesDirectoryExist_1)
{
    char        *d;
    int         r;
    struct stat st;
 ENTRY_LABEL(__doesDirectoryExist_1)
    d = to_string(sp[0]);
    r = stat(d, &st);
    free(d);
    sp += 2;
    RETURN((!r && (st.st_mode & S_IFDIR) ? prelude_True : prelude_False));
}

FUNCTION(__doesFileExist)
{
    EXPORT_LABEL(__doesFileExist)
 ENTRY_LABEL(__doesFileExist)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__doesFileExist_1;
    GOTO(nf_string);
}

static
FUNCTION(__doesFileExist_1)
{
    char        *f;
    int         r;
    struct stat st;
 ENTRY_LABEL(__doesFileExist_1)
    f = to_string(sp[0]);
    r = stat(f, &st);
    free(f);
    sp += 2;
    RETURN((r || (st.st_mode & S_IFDIR) ? prelude_False : prelude_True));
}

#line 489 "directory.nw"
DECLARE_ENTRYPOINT(__getModificationTime);
DECLARE_LABEL(__getModificationTime_1);

FUNCTION(__getModificationTime)
{
    EXPORT_LABEL(__getModificationTime)
 ENTRY_LABEL(__getModificationTime)
    CHECK_STACK1();
    sp   -= 1;
    sp[0] = sp[1];
    sp[1] = (Node *)__getModificationTime_1;
    GOTO(nf_string);
}

static
FUNCTION(__getModificationTime_1)
{
    char        *f;
    int         r;
    struct stat st;
    Node        *t;
 ENTRY_LABEL(__getModificationTime_1)
    f = to_string(sp[0]);
    r = stat(f, &st);
    free(f);
    if ( r )
    {
        sp[0] = from_string(strerror(errno));
        GOTO(__ioError);
    }
    sp += 2;

#if ONLY_BOXED_OBJECTS
    CHECK_HEAP(int_node_size);
    t       = (Node *)hp;
    t->info = &int_info;
    t->i.i  = st.st_mtime;
    hp     += int_node_size;
#else
    t = mk_int(st.st_mtime);
#endif
    RETURN(t);
}
