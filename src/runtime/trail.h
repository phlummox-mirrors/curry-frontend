#line 21 "trail.nw"
typedef struct save_rec {
    word	 *addr;		/* address of updated node */
    word	 info;		/* old info vector */
    unsigned int ofs;		/* offset within node */
    word	 val;		/* saved value */
} SaveRec;

#line 37 "trail.nw"
extern SaveRec *trail_base, *trail_end;
extern SaveRec *tp;

extern void trail_overflow(void) __attribute__ ((noreturn));

#define CHECK_TRAIL1()	if ( tp == trail_end ) trail_overflow();
#define CHECK_TRAIL(n)	if ( tp + n > trail_end ) trail_overflow();

#line 71 "trail.nw"
extern void init_trail(unsigned int trail_size);

#line 111 "trail.nw"
#define INFO_OFS	((word *)&((Node *)0)->info - (word *)0)

#define DO_SAVE(v,f) do { \
    CHECK_TRAIL1(); \
    tp->addr = (word *)(v); \
    tp->info = tp->addr[INFO_OFS]; \
    tp->ofs  = (word *)&(v->f) - (word *)(v); \
    tp->val  = (word)(v->f); \
    tp++; \
} while (0)
#define SAVE(v,f) do { \
    if ( (word *)(v) < hlim && (word *)(v->f) < hlim ) \
	DO_SAVE(v,f); \
} while (0)

#line 134 "trail.nw"
#define RESTORE(oldTp) do { \
    while ( tp > oldTp ) { \
	--tp; \
	tp->addr[INFO_OFS] = tp->info; \
	tp->addr[tp->ofs]  = tp->val; \
    } \
} while (0)
