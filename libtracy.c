/*
 * libtracy.c -- function call tracing
 *
 * {{{
 * Dick Tracy helps you trace the functions called during the execution
 * of a program.  For each function call or exit it prints a message
 * either on stderr or with GLib's g_debug() if configured so.
 *
 * To use it you need to compile the part of the program you are interested in
 * with -finstrument-functions.  It can be the executable, a separate library
 * or a dlopen()ed DSO, or any of the object files thereof.  Debugging symbols
 * are not required, just don't strip the relevant binaries.  You can also use
 * it to trace C extensions and glue code of Python (or whatever) programs.
 * Having compiled so, you can run your program with `tracy'.  Instrumented
 * binaries are usable even if you're not tracing them, so you may want to
 * make them so by default (save for the performance penalty).
 *
 * You can limit the amount of information printed during tracing by setting
 * these environment variables (`tracy' is a convenience frontend for that):
 *
 * -- $TRACY_SIGNAL:	If 'y' or a signal number then only start tracing
 *			when SIGPROF or that specified signal is caught.
 *			Getting the same signal toggles tracing off again.
 * -- $TRACY_INLIBS:	A colon-separated list of basenames indicating
 *			calls to which DSOs to include in the output.
 *			Calls to DSOs not in this list will be omitted.
 *			Example: "libalpha.so:libbeta.so".
 * -- $TRACY_EXLIBS:	Likewise, but tells calls to which DSOs to exclude.
 *			In case both environment variables are defined
 *			$TRACY_INLIBS takes precedence.
 * -- $TRACY_INFUNS:	An extended glob pattern specifying which functions
 *			to report about.  Behaves similarly to $TRACY_INLIBS.
 *			Beyond '*' and '?' in an extended glob pattern you
 *			can describe alterations (':') and grouping ("()").
 *			Example: "foo_*:bar_*:baz_(alpha:beta)".
 * -- $TRACY_EXFUNS:	Like $TRACY_EXLIBS, but applies to functions.
 * -- $TRACY_MAXDEPTH:	Tells libtracy not to report function calls beyond
 *			a specific depth.  Suppose main()->foo()->bar()->
 *			baz() and $TRACY_MAXDEPTH is 2, only foo() and bar()
 *			are reported (unless they're excluded otherwise;
 *			excluded functions don't increase the depth, so if
 *			bar() was excluded baz() would be reported).
 * -- $TRACY_ASYNC:	Symbol resolution can slow down your program
 *			considerably.  In async mode while it is running
 *			libtracy will emit symbols addresses then a
 *			transformation table on exit().  You can resolve
 *			the symbol names with ares.pl afterwards.
 * -- $TRACY_LOG_ENTRIES_ONLY:
 *			Log only function entries.  This only unclutters output,
 *			but doesn't save much processing time.
 * -- $TRACY_LOG_TIME:	Include gettimeofday() of the call/return in the output.
 * -- $TRACY_LOG_TID:	Include the TID of the traced program in the output.
 *			Useful when you're tracing multiprocess/multithread
 *			programs.  WARNING: libtracy is NOT thread-safe!
 * -- $TRACY_LOG_FNAME:	Include the DSO's basename in the output (default).
 * -- $TRACY_LOG_INDENT: How many spaces to indent with each call level.
 *			 The default is 0, ie. start function names at the same
 *			 column in each call level.
 *
 * Compile this file as a shared library, but don't instrument it.
 * Specify -DCONFIG_GLIB to have it report with g_debug() (the log domain
 * will be "trace").  `tracinst' will take care of it all, if you don't mind.
 *
 * libtracy relies on being $LD_PRELOAD:ed to the program you want to trace.
 * (While this is problematic in scratchbox, there is a way out, and `tracy'
 * does exactly that.)  Then all instrumented functions call __cyg_profile_*()
 * automagically.  They use glibc's backtrace() to get the invocation points,
 * then go straight to the ELF headers and sections to deduce the function
 * names.  (This involves some heuristics---this is not a complete debugger.)
 *
 * To obey the $TRACY_* environment variables the fgrep- and extended glob
 * matching routines were written in the hope they would be faster than the
 * mainstream implementations.
 * }}}
 */

/* Configuration */
/* For dladdr() */
#define _GNU_SOURCE

/* Include files */
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <dlfcn.h>
#include <signal.h>

#include <elf.h>
#include <execinfo.h>

#include <sys/time.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/syscall.h>

#ifdef CONFIG_GLIB
# include <glib.h>
#else
# include <stdio.h>
#endif

/* Macros */
#define gettid()		(pid_t)syscall(SYS_gettid)

/* How to print the trace messages. */
#ifdef CONFIG_GLIB
# undef  G_LOG_DOMAIN
# define G_LOG_DOMAIN		"trace"
# define LOGIT(fmt, ...)	g_debug(fmt, ##__VA_ARGS__)
#else
# define LOGIT(fmt, ...)	fprintf(stderr, fmt "\n", ##__VA_ARGS__)
#endif

/* Type definitions {{{ */
/* Describes a word you can match against a path with match_words(). */
struct word_st
{
	/* Words are stored in a linked list.  Matching is sped up by
	 * precalculating a primitive hash (the unsigned sum of each
	 * character of .word). */
	unsigned hash, length;
	char const *word;
	struct word_st *next;
};

/* Holds all the information necessary to locate
 * the name of a function defined in a DSO. */
struct dso_st
{
	/*
	 * All fields point somewhere in the ELF image, thus not duplicated.
	 *
	 * -- fname:	Which DSO it belongs to.  
	 * -- strtab:	The relevant string table.  A string table is a
	 *		sequence of NIL-terminated strings, and the strings
	 *		are referred to by their position.  The table ends
	 *		at .strend.  ELFs have multiple string tables; this
	 *		is the one (the last), which is "likely" to contain
	 *		function names.
	 * -- symtab:	The DSO's (static) symbol table.
	 */
	char const *fname;
	char const *strtab, *strend;
	Elf32_Sym const *symtab, *symend;
	struct dso_st *next;
};
/* }}} */

/* Function prototypes */
static int match_eglob(char const *pattern, char const *str);

/* Private variables */
/* Is tracing enabled or are we waiting for a signal to start it? */
static int Tracing = 1;

/* Printed along with the trace messages. */
static unsigned int Callstack_depth = 0;

/* Temporary storage of addresses to resolve on exit. */
static int Async_fd = -1;

/* Program code */
/* fgrep matching {{{ */
/* Fills $word with information about (the basename of) $path. */
static void hash_path(struct word_st *word, char const *path)
{
	/* Fill $word such that it relates to the last component of $path. */
	word->word = path;
	word->hash = word->length = 0;
	while (*path)
	{
		if (*path != '/')
		{
			word->hash += (unsigned)*path++;
			word->length++;
		} else
		{	/* New path component, reset $word. */
			word->word = ++path;
			word->length = word->hash = 0;
		}
	} /* while */
} /* hash_path */

/*
 * Returns the basename of $path if it matches any of the $words,
 * otherwise returns NULL.  For low number of words this method
 * was found faster than using a GHashTable: (135450000 iterations)
 *
 * match_words():	14.780s
 * GHashTable:		23.178s
 */
static char const *match_words(struct word_st const *words, char const *path)
{
	struct word_st iword;

	if (!words)
		return 0;

	hash_path(&iword, path);
	do
	{
		if (iword.hash != words->hash)
			continue;
		else if (iword.length != words->length)
			continue;
		else if (memcmp(iword.word, words->word, iword.length))
			continue;
		else
			return iword.word;
	} while ((words = words->next) != NULL);

	return NULL;
} /* match_words */

/* Parses $str and returns its word_st representation used with match_words().
 * $str is expected to be a colon-separated list of file basenames. */
static struct word_st *mkwords(char const *str)
{
	struct word_st *first, *word;

	if (!*str)
		return NULL;

	/* Each basename in $str will be allocated a word_st. */
	if (!(word = first = malloc(sizeof(*word))))
	{
		LOGIT("malloc(%u): %m", sizeof(*word));
		return NULL;
	}
	word->word	= str;
	word->length	= word->hash = 0;
	word->next	= NULL;

	do
	{
		if (*str != ':')
		{	/* Update $word. */
			word->hash += (unsigned)*str++;
			word->length++;
		} else
		{	/* New word */
			if (!(word->next = malloc(sizeof(*word))))
			{
				LOGIT("malloc(%u): %m", sizeof(*word));
				break;
			}

			word		= word->next;
			word->word	= ++str;
			word->length	= word->hash = 0;
			word->next	= NULL;
		} /* if */
	} while (*str);

	return first;
} /* mkwords */
/* }}} */

/* (Extended) Glob matching {{{ */
/* Finds the first occurrence of $c in $str in the outermost grouping scope. */
static char const *find_end_of_glob(char const *str, char c)
{
	unsigned depth;

	depth = 0;
	for (; *str; str++)
	{
		if (depth == 0 && *str == c)
			return str + 1;
		else if (*str == '(')
			depth++;
		else if (*str == ')')
		{
			if (depth > 0)
				depth--;
			else
				return NULL;
		}
	} /* for */
	return NULL;
} /* find_end_of_glob */

/* Like match_eglob(), but doesn't support top-level alterations. */
static int match_glob(char const *pattern, char const *str)
{
	 /* The very basic idea is due to BWK from the Beautiful Code. */
	for (;;)
	{
		switch (*pattern)
		{
		case '(':
			/* Let match_eglob() sort it out. */
			pattern++;
			return match_eglob(pattern, str);
		case ')':
			/* Like below. */
			pattern++;
			break;
		case ':':
			/* An alternative matched, continue right after
			 * the alteration. */
			if ((pattern = find_end_of_glob(pattern, ')')) != NULL)
				break;
		case '\0':
			return !*str;

		case '*':
			/* Try to ignore more and more characters of $str
			 * until we're out of them. */
			pattern++;
			do
				if (match_glob(pattern, str))
					return 1;
			while (*str++);
			return 0;

		case '?':
			if (!*str++)
				return 0;
			pattern++;
			break;
		default:
			if (*str++ != *pattern++)
				return 0;
			break;
		} /* switch */
	} /* for */
} /* match_glob */

/*
 * Match $str against an extended glob $pattern, like:
 * "alpha:be(t:l)a:g*a:d???a:ep(x(xx:yy)y:z*z)silon:sig(ma:)",
 * where parenthesis denote grouping and colons delimit alternatives.
 *
 * This implementation was found at least as fast as mainstream
 * library routines while being way smarter.  The slightly less
 * flexible match_glob() "backend" beat them all, to death.
 * (These results are all for non-overcomplicated patterns
 * like "libg*2.0.*" which don't require too much backtracking.)
 *
 * match_glob():		   7.748s
 * match_eglob():		  18.083s
 * fnmatch():			  17.928s
 * g_pattern_match_string():	  16.391s
 * g_pattern_match_simple():	1:22.820s
 */
static int match_eglob(char const *pattern, char const *str)
{
	do
		if (match_glob(pattern, str))
			return 1;
	while ((pattern = find_end_of_glob(pattern, ':')) != NULL);
	return 0;
} /* match_eglob */
/* }}} */

/* Function name resolution {{{ */
/* If $addr is defined by $dso, returns its function name.
 * $base is the where the DSO is loaded in the memory. */
static char const *getsym(struct dso_st const *dso,
	void const *base, void const *addr)
{
	char const *name;
	unsigned diff, now;
	Elf32_Sym const *closest, *sym;

	/* $dso->symtab tells where the functions begin, but $addr
	 * may point anywhere inside the function.  We need to find
	 * the function defined closest to $addr. */
	diff = 0;
	closest = NULL;
	for (sym = dso->symtab; sym < dso->symend; sym++)
	{
		Elf32_Addr eddr;

		/*
		 * In the symtabs of libraries and dlopen()ed DSOs there are
		 * offsets, relative to $base, but for the executable they
		 * are true memory locations.  $eddr is $addr, comparable with
		 * sym->st_value.
		 */
		eddr = sym->st_value > base-NULL
			? addr-NULL : addr-base;

		/* Only addresses *below* the function entry point may
		 * belong to it. */
		if (eddr < sym->st_value)
			continue;

		now = eddr - sym->st_value;
		if (!closest || diff > now)
		{
			if (dso->strtab + sym->st_name >= dso->strend)
				continue;
			if (*(dso->strtab + sym->st_name) == '$')
				continue;
			closest = sym;
			diff = now;
			if (diff == 0)
				break;
		}
	} /* for */

	if (!closest)
		return NULL;

	/* Finally, look up the name of the $closest symbol. */
	name = dso->strtab + closest->st_name;
	return name < dso->strend ? name : NULL;
} /* getsym */

/* Processes $file, an ELF image, and tries to find
 * its string and symbol tables. */
static int getelf(struct dso_st *dso, void const *file)
{
	unsigned i;
	Elf32_Ehdr const *elf;
	Elf32_Shdr const *sec, *strsec, *symsec;

	/* Is it ELF at all?  NOTE that we're not 64bit-aware. */
	elf = file;
	if (elf->e_ident[0] != ELFMAG0 || elf->e_ident[1] != ELFMAG1)
		return 0;
	if (elf->e_ident[2] != ELFMAG2 || elf->e_ident[3] != ELFMAG3)
		return 0;

	/* Find the string and symbol tables. */
	strsec = symsec = NULL;
	for (i = 0, sec = file + elf->e_shoff; i < elf->e_shnum; i++, sec++)
		if (sec->sh_type == SHT_STRTAB)
			strsec = sec;
		else if (sec->sh_type == SHT_SYMTAB)
			symsec = sec;

	/* Sanity checking. */
	if (!strsec || !symsec)
		return 0;
	if (symsec->sh_entsize != sizeof(Elf32_Sym))
		return 0;

	/* All is well, fill $dso. */
	dso->strtab = file + strsec->sh_offset;
	dso->strend = (void const *)dso->strtab + strsec->sh_size;
	dso->symtab = file + symsec->sh_offset;
	dso->symend = (void const *)dso->symtab + symsec->sh_size;

	return 1;
} /* getelf */

/* Fills $dso with information from $fname. */
static int getdso(struct dso_st *dso, char const *fname,
	int *hfilep, void const **filep, off_t *fsizep)
{
	int hfile;
	struct stat sbuf;
	void const *file;

	/* mmap() $fname and process its ELF headers.  If it cannot be found
	 * and $fname is relative assume this is the executable itself and
	 * open it from /proc.  Seems $fname is argv[0] these cases. */
	if ((hfile = open(fname, O_RDONLY)) < 0 && (fname[0] == '/'
			|| (hfile = open("/proc/self/exe", O_RDONLY)) < 0))
		goto out0;
	else if (fstat(hfile, &sbuf) < 0)
		goto out1;
	else if ((file = mmap(NULL, sbuf.st_size, PROT_READ, MAP_SHARED,
			hfile, 0)) == MAP_FAILED)
		goto out1;
	else if (!getelf(dso, file))
		goto out2;

	/* Also return $hfile etc. to allow the caller to munmap() it. */
	dso->fname = fname;
	*hfilep    = hfile;
	*filep     = file;
	*fsizep    = sbuf.st_size;

	return 1;

	/* Clean up */
out2:	munmap((void *)file, sbuf.st_size);
out1:	close(hfile);
out0:	return 0;
} /* getdso */

/* Report decisions {{{ */
/* These routines belong to an upper layer, but performance justified
 * their presence here. */
/* Returns the basename of $fname if calls to it are to be reported. */
static char const *report_dso(char const *fname)
{
	static int report_all = 0;
	static struct word_st const *flist = NULL;
	static int is_whitelist;
	char const *base;

	/* Read the environment if we haven't. */
	if (!report_all && !flist)
	{
		char const *env;

		if      ((env=getenv("TRACY_INLIBS")) && (flist=mkwords(env)))
			is_whitelist = 1;
		else if ((env=getenv("TRACY_EXLIBS")) && (flist=mkwords(env)))
			is_whitelist = 0;
		else
			report_all = 1;
	}

	/* Match against $flist if we have one. */
	if (!report_all)
	{
		if ((base = match_words(flist, fname)) != NULL)
			return is_whitelist ? base : NULL;
		else if (is_whitelist)
			return NULL;
	}

	/* Return the basename of $fname. */
	return (!(base = strrchr(fname, '/'))) ? fname : base + 1;
} /* report_dso */

/* Returns whether to report a call to $funame.  If $funame is NULL,
 * returns 0 if there's whitelisting. */
static int report_function(char const *funame)
{
	static int report_all = 0;
	static char const *pattern = NULL;
	static int is_whitelist;

	/* Read the environment if we haven't. */
	if (!report_all && !pattern)
	{
		if      ((pattern = getenv("TRACY_INFUNS")) && pattern[0])
			is_whitelist = 1;
		else if ((pattern = getenv("TRACY_EXFUNS")) && pattern[0])
			is_whitelist = 0;
		else
			report_all = 1;
	}

	if (report_all)
		return 1;
	else if (funame && match_eglob(pattern, funame))
		return  is_whitelist;
	else
		return !is_whitelist;
} /* report_function */
/* }}} */

/*
 * Sets $funamep to the name of the function $addr is contained within.
 * If $fnamep is not NULL sets it to the name of the DSO where function
 * is defined.  Returns 1 if everything is OK, 0 if the name was not
 * found, or -1 if it is not to be reported.
 */
static int addr2name(char const **fnamep, char const **funamep,
	void const *addr)
{
	static struct dso_st *seen;
	Dl_info info;
	char const *fname;
	struct dso_st *dso;

	/* Find the file that defined the function of $addr. */
	if (fnamep)
		*fnamep = "[???]";
	if (!dladdr(addr, &info))
		/* We're in trouble, don't do anything. */
		return report_function(NULL) ? 0 : -1;
	if (!info.dli_fname)
		/* Should not happen either. */
		return report_function(NULL) ? 0 : -1;

	/* Check whether calls to this DSO is to be reported here
	 * to avoid opening it unnecessarily. */
	if (!(fname = report_dso(info.dli_fname)))
		return -1;
	if (fnamep)
		*fnamep = fname;

	if (info.dli_sname)
	{
		/* dladdr() managed to do the hard work for us. */
		*funamep = info.dli_sname;
		return report_function(*funamep) ? 1 : -1;
	} else if (info.dli_saddr)
		/* info.dli_addr may be more accurate than $addr. */
		addr = info.dli_saddr;

	/* It is up to us to find out the function name from info.dli_fname.
	 * First we need to get contextual information we cache in $seen. */
	for (dso = seen; ; dso = dso->next)
	{
		if (dso == NULL)
		{
			int hfile;
			off_t fsize;
			void const *file;
			struct dso_st newdso;

			/* Never saw this DSO before, let's meet.
			 * TODO I think .dli_fname becomes incorrect
			 * if the program chdir()ed elsewhere. */
			if (!getdso(&newdso, info.dli_fname,
					&hfile, &file, &fsize))
				return report_function(NULL) ? 0 : -1;
			*funamep = getsym(&newdso, info.dli_fbase, addr);

			/* Try to remember it. */
			if ((dso = malloc(sizeof(*dso))) != NULL)
			{
				memcpy(dso, &newdso, sizeof(*dso));
				dso->next = seen;
				seen = dso;
			} else
			{	/* Failed, clean up what getdso() did. */
				LOGIT("malloc(%u): %m", sizeof(*dso));
				munmap((void *)file, fsize);
				close(hfile);
			}

			return report_function(*funamep)
				? *funamep != NULL : -1;
		} else if (dso->fname == info.dli_fname)
		{
			/* info.dli_fname pointers point to some program
			 * header and are the same for all invocations. */
			*funamep = getsym(dso, info.dli_fbase, addr);
			return report_function(*funamep)
				? *funamep != NULL : -1;
		} /* if */
	} /* for */
} /* addr2name */
/* }}} */

/* Printing the trace {{{ */
static char const *procinfo(void)
{
	static int need_time = -1, need_tid = -1;
	static char pi[64];
	struct timeval tv;

	if (need_time < 0)
	{
		char const *env;

		need_time = (env = getenv("TRACY_LOG_TIME")) && env[0] == '1';
		need_tid  = (env = getenv("TRACY_LOG_TID"))  && env[0] == '1';
	}

	if (!need_time && !need_tid)
	{
		/* NOP */
	} else if (need_time && !need_tid)
	{
		gettimeofday(&tv, NULL);
		sprintf(pi, "%lu.%06lu ", tv.tv_sec, tv.tv_usec);
	} else if (!need_time && need_tid)
	{
		sprintf(pi, "%u ", gettid());
	} else
	{
		gettimeofday(&tv, NULL);
		sprintf(pi, "%lu.%06lu[%u] ", tv.tv_sec, tv.tv_usec, gettid());
	}

	return pi;
}

/* Print the symbol address => name resolution table in $TRACY_ASYNC mode. */
static void resolve_backlog(void)
{
	void *addr;

	/* A lot of entries will be duplicate but nevermind. */
	LOGIT("SYMTAB:");
	lseek(Async_fd, SEEK_SET, 0);
	while (read(Async_fd, &addr, sizeof(addr)) == sizeof(addr))
	{
		char const *fname, *funame;

		switch (addr2name(&fname, &funame, addr))
		{
		case 1:
			LOGIT("%p = %s:%s()", addr, fname, funame);
			break;
		case 0:
			LOGIT("%p = %s:[%p]", addr, fname, addr);
			break;
		}
	}
	close(Async_fd);
}

/* Determines which function the control flow entered/left
 * and prints the trace message. */
static int print_trace(void *addr, char const *dir)
{
	static unsigned depth_limit;
	static int depth_limited = -1, be_async = -1, entries_only = -1;
	static int indent = -1, log_fname = -1;
	char const *env, *colon, *fname, *funame;
	int is_entry, success;

	/* Read $TRACY_MAXDEPTH if we haven't. */
	if (depth_limited < 0)
	{
		if ((env = getenv("TRACY_MAXDEPTH")) && env[0])
		{
			depth_limit = atoi(env);
			depth_limited = 1;
		} else
			depth_limited = 0;
	}

	/* Have we reached the limit? */
	if (depth_limited && Callstack_depth >= depth_limit)
		return 1;

#ifndef __ARMEL__
	{
		void *addrs[3];

		/*
		 * In the frame:
		 * [0] this function,
		 * [1] the instrumentation function,
		 * [2] the function we're interested in.
		 *
		 * On ARM backtrace() is unreliable, so use $addr directly.
		 * On x86 we can't avoid this call.
		 */
		if (backtrace(addrs, 3) < 3)
			return 1;
		addr = addrs[2];
	}
#endif /* ! __ARMEL__ */

	/* In async mode create a temporary file where we can write symbol
	 * addresses the program encounters on function calls enters. */
	if (be_async < 0)
	{
		be_async = (env = getenv("TRACY_ASYNC")) && env[0] == '1';
		if (be_async)
		{
			static char tmpfname[] = "/tmp/tracy.XXXXXX";

			if ((Async_fd = mkstemp(tmpfname)) < 0)
			{
				LOGIT("mkstemp: %m");
				be_async = 0;
			} else
			{
				unlink(tmpfname);
				atexit(resolve_backlog);
			}
		}
	} /* be_async? */

	/* Log only function entries? */
	is_entry = dir[0] == 'E';
	if (entries_only < 0)
		entries_only = (env = getenv("TRACY_LOG_ENTRIES_ONLY"))
			&& env[0] == '1';
	if (entries_only)
		dir = "";

	/* Get how much to indent $fname:$funame. */
	if (indent < 0)
		indent = (env = getenv("TRACY_LOG_INDENT")) ? atoi(env) : 0;

	/* Write the async file if necessary. */
	if (Async_fd >= 0)
	{	/* resolve_backlog() will resolve $addr when we exit. */
		if (!entries_only || is_entry)
			LOGIT("%s%s[%u]%*s[%p]", procinfo(), dir,
				Callstack_depth,
				1 + indent*Callstack_depth, " ", addr);
		if (is_entry)
			/* Try not to bloat the file, it'll have
			 * lots of identical entries anyway. */
			write(Async_fd, &addr, sizeof(addr));
		return 1;
	}

	/* Resolve $addr. */
	if ((success = addr2name(&fname, &funame, addr)) < 0)
		/* Omitted from output, don't count it in $Callstack_depth. */
		return 0;

	/* Don't log LEAVE:s if $entries_only. */
	if (entries_only && !is_entry)
		return 1;

	/* Print or omit the "<$fname>:" in front of $funame? */
	if (log_fname < 0)
		log_fname = (env = getenv("TRACY_LOG_FNAME")) ? env[0] == '1' : 1;
	if (log_fname)
		colon = ":";
	else
		fname = colon = "";

	/* Log the damn thing. */
	if (success)
		LOGIT("%s%s[%u]%*s%s%s%s()", procinfo(),
			dir, Callstack_depth, 1 + indent*Callstack_depth, " ",
			fname, colon, funame);
	else
		LOGIT("%s%s[%u]%*s%s%s[%p]", procinfo(),
			dir, Callstack_depth, 1 + indent*Callstack_depth, " ",
			fname, colon, addr);

	/* We've logged something. */
	return 1;
} /* print_trace */

/* The functions below are invoked automatically by code generated
 * by the compiler.  These are the entry points of the library. */
void __cyg_profile_func_enter(void *self, void *callsite)
{
	if (!Tracing)
		return;
	if (print_trace(self, "ENTER"))
		Callstack_depth++;
}

void __cyg_profile_func_exit(void *self, void *callsite)
{
	if (!Tracing)
		return;
	Callstack_depth--;
	if (!print_trace(self, "LEAVE"))
		Callstack_depth++;
}
/* }}} */

/* Initialization {{{ */
static void toggle_tracing(int signum)
{
	Tracing = !Tracing;
}

/* Start tracing or install a signal handler to start it later. */
static __attribute__((constructor))
void tracy_init(void)
{
   char const *env;

   env = getenv("TRACY_SIGNAL");
   if (env)
   {
	   int signum;

	   if (env[0] == 'y' || env[0] == 'Y')
		   signum = SIGPROF;
	   else if ((signum = atoi(env)) <= 0)
		   LOGIT("couldn't understand $TRACY_SIGNAL=%s", env);
	   signal(signum, toggle_tracing);
	   Tracing = 0;
   }
}
/* }}} */

/* vim: set foldmethod=marker: */
/* End of libtracy.c */
