#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include <threads/fixed-point.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;
 
/* List of processes in THREAD_BLOCK state, that is, processes
   that are not ready to run that is they are sleeping. */
static struct list blocked_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/*Lock used by thread_block */
static struct lock blocked_lock;

/*Int to store the next waeup time*/
static int64_t next_wakeup;
/* Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
  };

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

static int load_avg;            /* Average number of threads ready to run over the past minute */      



/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static struct thread *managerial_thread; /* Thread that unblock the threads blocked on alarms */
static void managerial_wakeup (void *aux UNUSED); 

static struct thread *managerial_thread_2; /* Thread that calculates recent_cpu and load_avg on each thread in all_list on every 100th tick. */
static void managerial_wakeup_2 (void *aux UNUSED); 

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  ASSERT (intr_get_level () == INTR_OFF);

  lock_init (&tid_lock);
  lock_init (&blocked_lock);
  list_init (&ready_list);
  list_init (&blocked_list);
  list_init (&all_list);
  load_avg=0;
  next_wakeup=INT64_MAX;
  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);

  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
  thread_create("managerial_thread", PRI_MAX, managerial_wakeup, NULL); 
  thread_create("managerial_thread_2", PRI_MAX, managerial_wakeup_2, NULL); 
  
}

/*  On each timer tick, the running thread’s recent cpu is incremented by 1. */
void 
cpu_increase (void)
{
  if (thread_current() == idle_thread || thread_current() == managerial_thread || thread_current() == managerial_thread_2) return;
  thread_current ()->recent_cpu = add_x_and_n (thread_current ()->recent_cpu, 1);
}
/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) 
{
  struct thread *t = thread_current ();
  
  
  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;
int64_t ticks = timer_ticks();
	
  /*Check if sleepers list is empty or not.*/
    /*if list isn't empty then compare current time to the next_wake_up.*/
	/* checks if current tick is equal to the next_wakeup and managerial thread is blocked */  
    if(timer_ticks() == next_wakeup && managerial_thread->status==THREAD_BLOCKED)
    	thread_unblock(managerial_thread);
	
	/* checks if thread_mlfqs is ON and timer ticks is positive */
    if(thread_mlfqs && timer_ticks() > 0)
    {
      /* Increments the recent_cpu value of the current running thread */	
      cpu_increase();
      
      /* Checks if timer ticks is a multiple of TIMER FREQ (i.e. 100) to unblock managerial_thread_2 to perform mlfqs */
      if(timer_ticks() % TIMER_FREQ== 0)
      {
        if(thread_current()->priority != PRI_MIN) thread_current()->priority = thread_current()->priority - 1;
        
        if(managerial_thread_2 && managerial_thread_2->status == THREAD_BLOCKED)
          thread_unblock(managerial_thread_2);      
      }
      	/* Checks if timer_tick is a multiple of TIME_SLICE (i.e. 4) to decrement the priority of current thread by 1 to implement Preemption. */
       else if (timer_ticks() % TIME_SLICE == 0)
      {
     
        if(thread_current()->priority != PRI_MIN) thread_current()->priority = thread_current()->priority - 1;
 
      }
    }
  
  if (++thread_ticks >= TIME_SLICE)
    intr_yield_on_return ();
}

/* Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;
  enum intr_level old_level;

  ASSERT (function != NULL);

  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();

  /* Prepare thread for first run by initializing its stack.
     Do this atomically so intermediate values for the 'stack' 
     member cannot be observed. */
  old_level = intr_disable ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;



  intr_set_level (old_level);

  /* Add to run queue. */
  thread_unblock (t);
  thread_check_for_yield();
 
  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);
  list_insert_ordered(&ready_list, &(t->elem),ready_list_sort,NULL);
  t->status = THREAD_READY;
  intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it call schedule_tail(). */
  intr_disable ();
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread) 
  list_insert_ordered (&ready_list, &cur->elem,ready_list_sort,NULL);
    //list_push_back(&ready_list, &cur->elem);
  cur->status = THREAD_READY;
  schedule ();
  intr_set_level (old_level);
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) 
{
 
   enum intr_level prev_level = intr_disable();
  struct thread *th=thread_current ();
 
  th->priority = new_priority;
  th->initial_priority=th->priority;/*storing it here as may get changed after donation*/
  thread_donate(th);/*donate priority*/
  thread_check_for_yield();/*priority of current thread changing so need to check*/
  intr_set_level(prev_level);
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) 
{
  return thread_current ()->priority;
}

/* Sets the current thread’s nice value to "nice" and recalculates the thread’s priority based on the new value */
void
thread_set_nice (int nice UNUSED) 
{
  struct thread *t = thread_current ();
  t->nice = nice;
  thread_update_priority (t);
  /*  If the running thread no longer has the highest priority, yields */
  thread_check_for_yield(); 
 
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  return thread_current()->nice;
}

/*Returns 100 times the current system load average, rounded to the nearest integer*/
int
thread_get_load_avg (void) 
{
  enum intr_level prev_level = intr_disable ();
  int avg = convert_x_to_integer_nearest (multiply_x_by_n (load_avg, 100) );
  intr_set_level (prev_level);
  return avg; 
}

/* Returns 100 times the current thread’s recent cpu value, rounded to the nearest integer*/
int
thread_get_recent_cpu (void) 
{
  enum intr_level prev_level = intr_disable ();
  int avg = convert_x_to_integer_nearest (multiply_x_by_n (thread_current ()->recent_cpu, 100) );
  intr_set_level (prev_level);
  return avg;
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /* The scheduler runs with interrupts off. */
  function (aux);       /* Execute the thread function. */
  thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  sema_init (&t->execute, 0);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  t->stack = (uint8_t *) t + PGSIZE;
  t->priority = priority;
  t->nice = 0;
  t->recent_cpu=0;
  t->magic = THREAD_MAGIC;
  t->initial_priority=priority;
  list_init(&t->lock_list);
  t->lock_seek=NULL; 
  list_push_back (&all_list, &t->allelem);
  if (t != initial_thread)
  {
    t->parent = thread_current();
    list_push_back (&(t->parent->children), &t->parent_elem);
  }
   else
   { t->parent = NULL;}
  
  list_init (&t->children);
  sema_init (&t->exec, 0);
  sema_init (&t->wait, 0);
  t->return_status = -1;
  t->load_complete = false;
  t->executable = NULL;
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) 
{
  if (list_empty (&ready_list))
    return idle_thread;
  else
    return list_entry (list_pop_front (&ready_list), struct thread, elem);
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
schedule_tail (struct thread *prev) 
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until schedule_tail() has
   completed. */
static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  schedule_tail (prev); 
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}



/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);



/* Our versions of code */


/*  Sorts blocked list in ascending order of wake up time*/
bool blocked_sort(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  return list_entry(a, struct thread, elem)->wake_at < list_entry(b, struct thread, elem)->wake_at;
}


/*  Sorts ready list in descending order of  priority*/
bool ready_list_sort(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  return list_entry(a, struct thread, elem)->priority > list_entry(b, struct thread, elem)->priority;
}


/* Sets the priority of current thread to maximum value so that when it gets unblocked 
  it starts running and also stores the previous priority value.*/
void thread_priority_temporarily_up(void)
{
	struct thread *t=thread_current();
	t->prev_priority=t->priority;
	t->priority =PRI_MAX;
}


/* Restores the previous priority of the current running thread */
void thread_priority_restore(void)
{
	struct thread *t=thread_current();
	t->priority =t->prev_priority;
}


/*
  When an interrupt comes,the current running thread is supposed to be blocked.
  It acquires the lock so that no other thread can access the blocked list.
  Then we insert it in blocking list based on its wakeup time and update the next_wakeup
*/
void  thread_block_till (int64_t ticks, int64_t start)
{
  int64_t wakeup=ticks +start;
  struct thread *t=thread_current();

  enum intr_level prev_level;
  ASSERT(t->status==THREAD_RUNNING);
  prev_level=intr_disable();
  t->wake_at=wakeup;
 // lock_acquire(&blocked_lock);
  list_insert_ordered(&blocked_list, &(t->elem), blocked_sort, NULL);
  //lock_release(&blocked_lock);
  if(wakeup<=next_wakeup)
    next_wakeup=wakeup;
  thread_block();
  intr_set_level(prev_level);
}

/*
  We update the next wake up and also unblock all the threads whose wake up time is 
  less than the next_wakup. If threads have same wakeup time each thread will unblock 
  another thread recursively.
*/
void thread_set_next_wakeup(void)
{
  enum intr_level prev_level;
  prev_level = intr_disable ();
  lock_acquire(&blocked_lock);
  if(!list_empty (&blocked_list))
  {
    struct thread *t = list_entry (blocked_list.head.next,struct thread, elem);
    if (t->wake_at <= next_wakeup  && timer_ticks () >= next_wakeup)
    {
      list_pop_front(&blocked_list);
      thread_unblock(t);
    }
  }

  if (list_empty (&blocked_list))
  next_wakeup = INT64_MAX;
  else
  next_wakeup = list_entry(blocked_list.head.next,struct thread, elem)->wake_at;
  lock_release(&blocked_lock);
  intr_set_level (prev_level);
}


/*sorting locks in descending order of priority*/
bool lock_sort(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  return list_entry(a, struct lock, elem)->priority > list_entry(b, struct lock, elem)->priority;
}

/*If priority of threads in ready list is higher thread yield*/
void thread_check_for_yield(void)
{
  enum intr_level prev_level = intr_disable();
  
  if(!list_empty(&ready_list))
  {
    struct list_elem *head=list_front(&ready_list);
    struct thread *t = list_entry(head, struct thread, elem); 
    if(t->priority > thread_current()->priority)
    {
      thread_yield();
    }
  }
  intr_set_level(prev_level);
}

/*donating priority */
void thread_donate(struct thread *th)
{
  enum intr_level prev_level = intr_disable();
  thread_update(th);
  if(th->status==THREAD_READY)//  as priority changing again sort
  {
    list_sort(&ready_list,ready_list_sort,NULL);
  }
  intr_set_level(prev_level);
}

/*updating based on locks acquired */
void thread_update(struct thread *th)
{
  enum intr_level prev_level = intr_disable();
  int max=th->initial_priority;
  int prio;
  if(!list_empty(&th->lock_list))
  {
    list_sort(&th->lock_list,lock_sort,NULL);// acquired list is sorted based on priority of lock*/
    prio=list_entry(list_front(&th->lock_list),struct lock,elem)->priority;
    if(prio>max)
      max=prio;
  }
  th->priority=max;
  intr_set_level(prev_level);
}

void thread_acquire_lock(struct lock *lock)
{
  enum intr_level prev_level = intr_disable();
  list_insert_ordered(&thread_current()->lock_list,&lock->elem,lock_sort,NULL);
  int maxi=0;
  /*locks priority will be the first one of the list as already sorted*/
  if(!list_empty(&(lock->semaphore.waiters)))
  {
    maxi= list_entry( list_begin(&(lock->semaphore.waiters)),struct thread,elem)->priority;
  }
   lock->priority = maxi;
  intr_set_level(prev_level);
}

/* Thread releases the lock, once it has completed its task. */
void thread_release_lock(struct lock *lock)
{
  enum intr_level prev_level = intr_disable();
  list_remove(&lock->elem);
  thread_update(thread_current());/*as lock being removed again update */
  intr_set_level(prev_level);
}

/*  It will unblock all threads in the blocked list with the same wakeup time as the next_wakeup. */
void timer_wakeup ()
{
  lock_acquire (&blocked_lock);
  while (!list_empty (&blocked_list))
  {
    struct thread *t = list_entry (list_front (&blocked_list),
                                  struct thread, elem);
    if (t->wake_at <= next_wakeup)
    {
      list_pop_front(&blocked_list);
      thread_unblock(t);
    }
    else
      break;
  }

  if (list_empty (&blocked_list))
    next_wakeup = INT64_MAX;
  else
    next_wakeup = list_entry(list_front(&blocked_list),
                                struct thread, elem)->wake_at;
  lock_release (&blocked_lock);
}

/* This wakes up the appropriate blocked threads at each next_wakeup. */
void managerial_wakeup (void *aux UNUSED)
{
  managerial_thread = thread_current ();
  enum intr_level old_level;
  
  while (true)
  {
    old_level = intr_disable ();
    thread_block ();
    intr_set_level (old_level);

    timer_wakeup ();    
  }
}

/* Recalculates the Systems Load Average  */
/* load_avg = (59/60)*load_avg + (1/60)*ready_threads */
void calc_load_avg (void)
{
  int cnt = list_size (&ready_list);

  if(managerial_thread && managerial_thread->status == THREAD_READY)  cnt--;
  if(managerial_thread_2 && managerial_thread_2->status == THREAD_READY)  cnt--;
  
  if (thread_current() != idle_thread && thread_current() != managerial_thread && thread_current() != managerial_thread_2) cnt++;

  ASSERT(cnt >= 0)

  int t1 = divide_x_by_y (59, 60);
  t1 = multiply_x_by_y (t1, load_avg);
  int t2 = divide_x_by_y (cnt, 60);
  load_avg = add_x_and_y (t1, t2);


  ASSERT (load_avg >= 0)
}

/* Calculate the recent cpu time for the thread t */
/* recent_cpu = (2*load_avg)/(2*load_avg + 1) * recent_cpu + nice */
void calc_recent_cpu (struct thread *t)
{
  if (t == idle_thread || t == managerial_thread || t == managerial_thread_2) return;

  int t1 = multiply_x_by_n (2, load_avg);
  int t2 = t1 + convert_n_to_fixed_point (1);
  t1 = multiply_x_by_y (t1, t->recent_cpu);
  t1 = divide_x_by_y (t1, t2);
  t1 = add_x_and_n (t1, t->nice);
  
  t->recent_cpu = t1;
}

/* Calculate the priority of the thread t. */
/* priority = PRI_MAX - (recent_cpu / 4) - (nice * 2) */
void thread_update_priority (struct thread *t)
{
  if (t == idle_thread || t == managerial_thread || t == managerial_thread_2) return;
  
  int t1 = convert_n_to_fixed_point (PRI_MAX);
  int t2 = divide_x_by_n (t->recent_cpu, 4);
  int t3 = convert_n_to_fixed_point (multiply_x_by_n (t->nice, 2));
  t1 = substract_y_from_x (t1, t2);
  t1 = substract_y_from_x (t1, t3);
  
  /* In B.2 Calculating Priority : The result should be rounded down to the nearest integer (truncated). */
  t1 = convert_x_to_integer_zero (t1);

  if (t1 < PRI_MIN) t->priority = PRI_MIN;
  else if (t1 > PRI_MAX) t->priority = PRI_MAX;
  else  t->priority = t1;
}

/* Calcualte the priority for each thread in all the lists. */
void cpu_priority (void)
{
  /* Derived from 'thread_foreach' */
  struct list_elem *e;
  for (e = list_begin (&all_list); e != list_end (&all_list); e = list_next (e))
    {
      if(e == managerial_thread_2 || e == managerial_thread || e == idle_thread)
      {
        continue;
      }
      struct thread *t = list_entry (e, struct thread, allelem);
      calc_recent_cpu (t);
      thread_update_priority (t);
    }
 
    list_sort(&(ready_list), ready_list_sort, NULL);
}

/* Managerial Thread to manage the mlfqs. */
void managerial_wakeup_2(void *AUX)
{
  managerial_thread_2 = thread_current();

  while(true)
  {
    enum intr_level prev_level = intr_disable();
    
    cpu_priority ();
    calc_load_avg ();
    thread_block();
    intr_set_level(prev_level);

  }

}

/*From id finding out the child of the thread*/
struct thread *
get_child_from_id (int id)
{
  struct thread *t = thread_current ();
  struct list_elem *e;
  struct thread *child = NULL;
  
  for (e = list_begin (&t->children);
       e!= list_end (&t->children); e = list_next (e))
  {
    struct thread *this = list_entry (e, struct thread, parent_elem);
    if (this->tid == id)
    {
      child = this;
      break;
    }
  }
  return child;
}







