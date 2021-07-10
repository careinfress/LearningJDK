/*
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

/*
 * This file is available under and governed by the GNU General Public
 * License version 2 only, as published by the Free Software Foundation.
 * However, the following notice accompanied the original version of this
 * file:
 *
 * Written by Doug Lea with assistance from members of JCP JSR-166
 * Expert Group and released to the public domain, as explained at
 * http://creativecommons.org/publicdomain/zero/1.0/
 */

package java.util.concurrent;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.AbstractMap;
import java.util.Arrays;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Spliterator;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.locks.LockSupport;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.DoubleBinaryOperator;
import java.util.function.Function;
import java.util.function.IntBinaryOperator;
import java.util.function.LongBinaryOperator;
import java.util.function.Predicate;
import java.util.function.ToDoubleBiFunction;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntBiFunction;
import java.util.function.ToIntFunction;
import java.util.function.ToLongBiFunction;
import java.util.function.ToLongFunction;
import java.util.stream.Stream;
import jdk.internal.misc.Unsafe;

/**
 * A hash table supporting full concurrency of retrievals and
 * high expected concurrency for updates. This class obeys the
 * same functional specification as {@link java.util.Hashtable}, and
 * includes versions of methods corresponding to each method of
 * {@code Hashtable}. However, even though all operations are
 * thread-safe, retrieval operations do <em>not</em> entail locking,
 * and there is <em>not</em> any support for locking the entire table
 * in a way that prevents all access.  This class is fully
 * interoperable with {@code Hashtable} in programs that rely on its
 * thread safety but not on its synchronization details.
 *
 * <p>Retrieval operations (including {@code get}) generally do not
 * block, so may overlap with update operations (including {@code put}
 * and {@code remove}). Retrievals reflect the results of the most
 * recently <em>completed</em> update operations holding upon their
 * onset. (More formally, an update operation for a given key bears a
 * <em>happens-before</em> relation with any (non-null) retrieval for
 * that key reporting the updated value.)  For aggregate operations
 * such as {@code putAll} and {@code clear}, concurrent retrievals may
 * reflect insertion or removal of only some entries.  Similarly,
 * Iterators, Spliterators and Enumerations return elements reflecting the
 * state of the hash table at some point at or since the creation of the
 * iterator/enumeration.  They do <em>not</em> throw {@link
 * java.util.ConcurrentModificationException ConcurrentModificationException}.
 * However, iterators are designed to be used by only one thread at a time.
 * Bear in mind that the results of aggregate status methods including
 * {@code size}, {@code isEmpty}, and {@code containsValue} are typically
 * useful only when a map is not undergoing concurrent updates in other threads.
 * Otherwise the results of these methods reflect transient states
 * that may be adequate for monitoring or estimation purposes, but not
 * for program control.
 *
 * <p>The table is dynamically expanded when there are too many
 * collisions (i.e., keys that have distinct hash codes but fall into
 * the same slot modulo the table size), with the expected average
 * effect of maintaining roughly two bins per mapping (corresponding
 * to a 0.75 load factor threshold for resizing). There may be much
 * variance around this average as mappings are added and removed, but
 * overall, this maintains a commonly accepted time/space tradeoff for
 * hash tables.  However, resizing this or any other kind of hash
 * table may be a relatively slow operation. When possible, it is a
 * good idea to provide a size estimate as an optional {@code
 * initialCapacity} constructor argument. An additional optional
 * {@code loadFactor} constructor argument provides a further means of
 * customizing initial table capacity by specifying the table density
 * to be used in calculating the amount of space to allocate for the
 * given number of elements.  Also, for compatibility with previous
 * versions of this class, constructors may optionally specify an
 * expected {@code concurrencyLevel} as an additional hint for
 * internal sizing.  Note that using many keys with exactly the same
 * {@code hashCode()} is a sure way to slow down performance of any
 * hash table. To ameliorate impact, when keys are {@link Comparable},
 * this class may use comparison order among keys to help break ties.
 *
 * <p>A {@link Set} projection of a ConcurrentHashMap may be created
 * (using {@link #newKeySet()} or {@link #newKeySet(int)}), or viewed
 * (using {@link #keySet(Object)} when only keys are of interest, and the
 * mapped values are (perhaps transiently) not used or all take the
 * same mapping value.
 *
 * <p>A ConcurrentHashMap can be used as a scalable frequency map (a
 * form of histogram or multiset) by using {@link
 * java.util.concurrent.atomic.LongAdder} values and initializing via
 * {@link #computeIfAbsent computeIfAbsent}. For example, to add a count
 * to a {@code ConcurrentHashMap<String,LongAdder> freqs}, you can use
 * {@code freqs.computeIfAbsent(key, k -> new LongAdder()).increment();}
 *
 * <p>This class and its views and iterators implement all of the
 * <em>optional</em> methods of the {@link Map} and {@link Iterator}
 * interfaces.
 *
 * <p>Like {@link Hashtable} but unlike {@link HashMap}, this class
 * does <em>not</em> allow {@code null} to be used as a key or value.
 *
 * <p>ConcurrentHashMaps support a set of sequential and parallel bulk
 * operations that, unlike most {@link Stream} methods, are designed
 * to be safely, and often sensibly, applied even with maps that are
 * being concurrently updated by other threads; for example, when
 * computing a snapshot summary of the values in a shared registry.
 * There are three kinds of operation, each with four forms, accepting
 * functions with keys, values, entries, and (key, value) pairs as
 * arguments and/or return values. Because the elements of a
 * ConcurrentHashMap are not ordered in any particular way, and may be
 * processed in different orders in different parallel executions, the
 * correctness of supplied functions should not depend on any
 * ordering, or on any other objects or values that may transiently
 * change while computation is in progress; and except for forEach
 * actions, should ideally be side-effect-free. Bulk operations on
 * {@link Map.Entry} objects do not support method {@code setValue}.
 *
 * <ul>
 * <li>forEach: Performs a given action on each element.
 * A variant form applies a given transformation on each element
 * before performing the action.
 *
 * <li>search: Returns the first available non-null result of
 * applying a given function on each element; skipping further
 * search when a result is found.
 *
 * <li>reduce: Accumulates each element.  The supplied reduction
 * function cannot rely on ordering (more formally, it should be
 * both associative and commutative).  There are five variants:
 *
 * <ul>
 *
 * <li>Plain reductions. (There is not a form of this method for
 * (key, value) function arguments since there is no corresponding
 * return type.)
 *
 * <li>Mapped reductions that accumulate the results of a given
 * function applied to each element.
 *
 * <li>Reductions to scalar doubles, longs, and ints, using a
 * given basis value.
 *
 * </ul>
 * </ul>
 *
 * <p>These bulk operations accept a {@code parallelismThreshold}
 * argument. Methods proceed sequentially if the current map size is
 * estimated to be less than the given threshold. Using a value of
 * {@code Long.MAX_VALUE} suppresses all parallelism.  Using a value
 * of {@code 1} results in maximal parallelism by partitioning into
 * enough subtasks to fully utilize the {@link
 * ForkJoinPool#commonPool()} that is used for all parallel
 * computations. Normally, you would initially choose one of these
 * extreme values, and then measure performance of using in-between
 * values that trade off overhead versus throughput.
 *
 * <p>The concurrency properties of bulk operations follow
 * from those of ConcurrentHashMap: Any non-null result returned
 * from {@code get(key)} and related access methods bears a
 * happens-before relation with the associated insertion or
 * update.  The result of any bulk operation reflects the
 * composition of these per-element relations (but is not
 * necessarily atomic with respect to the map as a whole unless it
 * is somehow known to be quiescent).  Conversely, because keys
 * and values in the map are never null, null serves as a reliable
 * atomic indicator of the current lack of any result.  To
 * maintain this property, null serves as an implicit basis for
 * all non-scalar reduction operations. For the double, long, and
 * int versions, the basis should be one that, when combined with
 * any other value, returns that other value (more formally, it
 * should be the identity element for the reduction). Most common
 * reductions have these properties; for example, computing a sum
 * with basis 0 or a minimum with basis MAX_VALUE.
 *
 * <p>Search and transformation functions provided as arguments
 * should similarly return null to indicate the lack of any result
 * (in which case it is not used). In the case of mapped
 * reductions, this also enables transformations to serve as
 * filters, returning null (or, in the case of primitive
 * specializations, the identity basis) if the element should not
 * be combined. You can create compound transformations and
 * filterings by composing them yourself under this "null means
 * there is nothing there now" rule before using them in search or
 * reduce operations.
 *
 * <p>Methods accepting and/or returning Entry arguments maintain
 * key-value associations. They may be useful for example when
 * finding the key for the greatest value. Note that "plain" Entry
 * arguments can be supplied using {@code new
 * AbstractMap.SimpleEntry(k,v)}.
 *
 * <p>Bulk operations may complete abruptly, throwing an
 * exception encountered in the application of a supplied
 * function. Bear in mind when handling such exceptions that other
 * concurrently executing functions could also have thrown
 * exceptions, or would have done so if the first exception had
 * not occurred.
 *
 * <p>Speedups for parallel compared to sequential forms are common
 * but not guaranteed.  Parallel operations involving brief functions
 * on small maps may execute more slowly than sequential forms if the
 * underlying work to parallelize the computation is more expensive
 * than the computation itself.  Similarly, parallelization may not
 * lead to much actual parallelism if all processors are busy
 * performing unrelated tasks.
 *
 * <p>All arguments to all task methods must be non-null.
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/java.base/java/util/package-summary.html#CollectionsFramework">
 * Java Collections Framework</a>.
 *
 * @since 1.5
 * @author Doug Lea
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 */
/*
 * ConcurrentHashMap结构：哈希数组+链表/红黑树，key和value均不能为null
 * ConcurrentHashMap的操作方式跟HashMap是基本统一的，
 * 不同之处在于，ConcurrentHashMap是线程安全的，其中用到了无锁编程
 */
public class ConcurrentHashMap<K, V> extends AbstractMap<K, V> implements ConcurrentMap<K, V>, Serializable {
    
    /*
     * Overview:
     *
     * The primary design goal of this hash table is to maintain
     * concurrent readability (typically method get(), but also
     * iterators and related methods) while minimizing update
     * contention. Secondary goals are to keep space consumption about
     * the same or better than java.util.HashMap, and to support high
     * initial insertion rates on an empty table by many threads.
     *
     * This map usually acts as a binned (bucketed) hash table.  Each
     * key-value mapping is held in a Node.  Most nodes are instances
     * of the basic Node class with hash, key, value, and next
     * fields. However, various subclasses exist: TreeNodes are
     * arranged in balanced trees, not lists.  TreeBins hold the roots
     * of sets of TreeNodes. ForwardingNodes are placed at the heads
     * of bins during resizing. ReservationNodes are used as
     * placeholders while establishing values in computeIfAbsent and
     * related methods.  The types TreeBin, ForwardingNode, and
     * ReservationNode do not hold normal user keys, values, or
     * hashes, and are readily distinguishable during search etc
     * because they have negative hash fields and null key and value
     * fields. (These special nodes are either uncommon or transient,
     * so the impact of carrying around some unused fields is
     * insignificant.)
     *
     * The table is lazily initialized to a power-of-two size upon the
     * first insertion.  Each bin in the table normally contains a
     * list of Nodes (most often, the list has only zero or one Node).
     * Table accesses require volatile/atomic reads, writes, and
     * CASes.  Because there is no other way to arrange this without
     * adding further indirections, we use intrinsics
     * (jdk.internal.misc.Unsafe) operations.
     *
     * We use the top (sign) bit of Node hash fields for control
     * purposes -- it is available anyway because of addressing
     * constraints.  Nodes with negative hash fields are specially
     * handled or ignored in map methods.
     *
     * Insertion (via put or its variants) of the first node in an
     * empty bin is performed by just CASing it to the bin.  This is
     * by far the most common case for put operations under most
     * key/hash distributions.  Other update operations (insert,
     * delete, and replace) require locks.  We do not want to waste
     * the space required to associate a distinct lock object with
     * each bin, so instead use the first node of a bin list itself as
     * a lock. Locking support for these locks relies on builtin
     * "synchronized" monitors.
     *
     * Using the first node of a list as a lock does not by itself
     * suffice though: When a node is locked, any update must first
     * validate that it is still the first node after locking it, and
     * retry if not. Because new nodes are always appended to lists,
     * once a node is first in a bin, it remains first until deleted
     * or the bin becomes invalidated (upon resizing).
     *
     * The main disadvantage of per-bin locks is that other update
     * operations on other nodes in a bin list protected by the same
     * lock can stall, for example when user equals() or mapping
     * functions take a long time.  However, statistically, under
     * random hash codes, this is not a common problem.  Ideally, the
     * frequency of nodes in bins follows a Poisson distribution
     * (http://en.wikipedia.org/wiki/Poisson_distribution) with a
     * parameter of about 0.5 on average, given the resizing threshold
     * of 0.75, although with a large variance because of resizing
     * granularity. Ignoring variance, the expected occurrences of
     * list size k are (exp(-0.5) * pow(0.5, k) / factorial(k)). The
     * first values are:
     *
     * 0:    0.60653066
     * 1:    0.30326533
     * 2:    0.07581633
     * 3:    0.01263606
     * 4:    0.00157952
     * 5:    0.00015795
     * 6:    0.00001316
     * 7:    0.00000094
     * 8:    0.00000006
     * more: less than 1 in ten million
     *
     * Lock contention probability for two threads accessing distinct
     * elements is roughly 1 / (8 * #elements) under random hashes.
     *
     * Actual hash code distributions encountered in practice
     * sometimes deviate significantly from uniform randomness.  This
     * includes the case when N > (1<<30), so some keys MUST collide.
     * Similarly for dumb or hostile usages in which multiple keys are
     * designed to have identical hash codes or ones that differs only
     * in masked-out high bits. So we use a secondary strategy that
     * applies when the number of nodes in a bin exceeds a
     * threshold. These TreeBins use a balanced tree to hold nodes (a
     * specialized form of red-black trees), bounding search time to
     * O(log N).  Each search step in a TreeBin is at least twice as
     * slow as in a regular list, but given that N cannot exceed
     * (1<<64) (before running out of addresses) this bounds search
     * steps, lock hold times, etc, to reasonable constants (roughly
     * 100 nodes inspected per operation worst case) so long as keys
     * are Comparable (which is very common -- String, Long, etc).
     * TreeBin nodes (TreeNodes) also maintain the same "next"
     * traversal pointers as regular nodes, so can be traversed in
     * iterators in the same way.
     *
     * The table is resized when occupancy exceeds a percentage
     * threshold (nominally, 0.75, but see below).  Any thread
     * noticing an overfull bin may assist in resizing after the
     * initiating thread allocates and sets up the replacement array.
     * However, rather than stalling, these other threads may proceed
     * with insertions etc.  The use of TreeBins shields us from the
     * worst case effects of overfilling while resizes are in
     * progress.  Resizing proceeds by transferring bins, one by one,
     * from the table to the next table. However, threads claim small
     * blocks of indices to transfer (via field transferIndex) before
     * doing so, reducing contention.  A generation stamp in field
     * sizeCtl ensures that resizings do not overlap. Because we are
     * using power-of-two expansion, the elements from each bin must
     * either stay at same index, or move with a power of two
     * offset. We eliminate unnecessary node creation by catching
     * cases where old nodes can be reused because their next fields
     * won't change.  On average, only about one-sixth of them need
     * cloning when a table doubles. The nodes they replace will be
     * garbage collectable as soon as they are no longer referenced by
     * any reader thread that may be in the midst of concurrently
     * traversing table.  Upon transfer, the old table bin contains
     * only a special forwarding node (with hash field "MOVED") that
     * contains the next table as its key. On encountering a
     * forwarding node, access and update operations restart, using
     * the new table.
     *
     * Each bin transfer requires its bin lock, which can stall
     * waiting for locks while resizing. However, because other
     * threads can join in and help resize rather than contend for
     * locks, average aggregate waits become shorter as resizing
     * progresses.  The transfer operation must also ensure that all
     * accessible bins in both the old and new table are usable by any
     * traversal.  This is arranged in part by proceeding from the
     * last bin (table.length - 1) up towards the first.  Upon seeing
     * a forwarding node, traversals (see class Traverser) arrange to
     * move to the new table without revisiting nodes.  To ensure that
     * no intervening nodes are skipped even when moved out of order,
     * a stack (see class TableStack) is created on first encounter of
     * a forwarding node during a traversal, to maintain its place if
     * later processing the current table. The need for these
     * save/restore mechanics is relatively rare, but when one
     * forwarding node is encountered, typically many more will be.
     * So Traversers use a simple caching scheme to avoid creating so
     * many new TableStack nodes. (Thanks to Peter Levart for
     * suggesting use of a stack here.)
     *
     * The traversal scheme also applies to partial traversals of
     * ranges of bins (via an alternate Traverser constructor)
     * to support partitioned aggregate operations.  Also, read-only
     * operations give up if ever forwarded to a null table, which
     * provides support for shutdown-style clearing, which is also not
     * currently implemented.
     *
     * Lazy table initialization minimizes footprint until first use,
     * and also avoids resizings when the first operation is from a
     * putAll, constructor with map argument, or deserialization.
     * These cases attempt to override the initial capacity settings,
     * but harmlessly fail to take effect in cases of races.
     *
     * The element count is maintained using a specialization of
     * LongAdder. We need to incorporate a specialization rather than
     * just use a LongAdder in order to access implicit
     * contention-sensing that leads to creation of multiple
     * CounterCells.  The counter mechanics avoid contention on
     * updates but can encounter cache thrashing if read too
     * frequently during concurrent access. To avoid reading so often,
     * resizing under contention is attempted only upon adding to a
     * bin already holding two or more nodes. Under uniform hash
     * distributions, the probability of this occurring at threshold
     * is around 13%, meaning that only about 1 in 8 puts check
     * threshold (and after resizing, many fewer do so).
     *
     * TreeBins use a special form of comparison for search and
     * related operations (which is the main reason we cannot use
     * existing collections such as TreeMaps). TreeBins contain
     * Comparable elements, but may contain others, as well as
     * elements that are Comparable but not necessarily Comparable for
     * the same T, so we cannot invoke compareTo among them. To handle
     * this, the tree is ordered primarily by hash value, then by
     * Comparable.compareTo order if applicable.  On lookup at a node,
     * if elements are not comparable or compare as 0 then both left
     * and right children may need to be searched in the case of tied
     * hash values. (This corresponds to the full list search that
     * would be necessary if all elements were non-Comparable and had
     * tied hashes.) On insertion, to keep a total ordering (or as
     * close as is required here) across rebalancings, we compare
     * classes and identityHashCodes as tie-breakers. The red-black
     * balancing code is updated from pre-jdk-collections
     * (http://gee.cs.oswego.edu/dl/classes/collections/RBCell.java)
     * based in turn on Cormen, Leiserson, and Rivest "Introduction to
     * Algorithms" (CLR).
     *
     * TreeBins also require an additional locking mechanism.  While
     * list traversal is always possible by readers even during
     * updates, tree traversal is not, mainly because of tree-rotations
     * that may change the root node and/or its linkages.  TreeBins
     * include a simple read-write lock mechanism parasitic on the
     * main bin-synchronization strategy: Structural adjustments
     * associated with an insertion or removal are already bin-locked
     * (and so cannot conflict with other writers) but must wait for
     * ongoing readers to finish. Since there can be only one such
     * waiter, we use a simple scheme using a single "waiter" field to
     * block writers.  However, readers need never block.  If the root
     * lock is held, they proceed along the slow traversal path (via
     * next-pointers) until the lock becomes available or the list is
     * exhausted, whichever comes first. These cases are not fast, but
     * maximize aggregate expected throughput.
     *
     * Maintaining API and serialization compatibility with previous
     * versions of this class introduces several oddities. Mainly: We
     * leave untouched but unused constructor arguments referring to
     * concurrencyLevel. We accept a loadFactor constructor argument,
     * but apply it only to initial table capacity (which is the only
     * time that we can guarantee to honor it.) We also declare an
     * unused "Segment" class that is instantiated in minimal form
     * only when serializing.
     *
     * Also, solely for compatibility with previous versions of this
     * class, it extends AbstractMap, even though all of its methods
     * are overridden, so it is just useless baggage.
     *
     * This file is organized to make things a little easier to follow
     * while reading than they might otherwise: First the main static
     * declarations and utilities, then fields, then main public
     * methods (with a few factorings of multiple public methods into
     * internal ones), then sizing methods, trees, traversers, and
     * bulk operations.
     */
    
    
    /**
     * The default concurrency level for this table.
     * Unused but defined for compatibility with previous versions of this class.
     */
    // jdk1.7遗留下来的，用来表示并发级别的属性
    // jdk1.8只有在初始化的时候用到，不再表示并发级别了~ 1.8以后并发级别由散列表长度决定
    private static final int DEFAULT_CONCURRENCY_LEVEL = 16;    // 默认并发级别，未使用，只是为与该类的先前版本兼容
    
    /**
     * The largest possible (non-power of two) array size.
     * Needed by toArray and related methods.
     */
    // 最大的数组大小（非2的幂） toArray和相关方法需要(并不是核心属性)
    static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;    // 哈希数组最大容量(用于toArray中的阈值判断)
    
    /**
     * The largest possible table capacity.  This value must be
     * exactly 1<<30 to stay within Java array allocation and indexing
     * bounds for power of two table sizes, and is further required
     * because the top two bits of 32bit hash fields are used for
     * control purposes.
     */
    // 散列表数组最大容量值
    private static final int MAXIMUM_CAPACITY = 1 << 30;        // 哈希数组最大容量
    
    /**
     * The default initial table capacity.  Must be a power of 2
     * (i.e., at least 1) and at most MAXIMUM_CAPACITY.
     */
    private static final int DEFAULT_CAPACITY = 16;             // 哈希数组默认容量
    
    /**
     * The load factor for this table. Overrides of this value in
     * constructors affect only the initial table capacity.  The
     * actual floating point value isn't normally used -- it is
     * simpler to use expressions such as {@code n - (n >>> 2)} for
     * the associated resizing threshold.
     */
    // 负载因子：表示散列表的填满程度~ 在ConcurrentHashMap中，该属性是固定值0.75，不可修改~
    private static final float LOAD_FACTOR = 0.75f;     // ConcurrentHashMap默认装载因子（负荷系数）
    
    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2, and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     */
    // 树化阈值：散列表的一个桶中链表长度达到8时候，可能发生链表树化
    static final int TREEIFY_THRESHOLD = 8;     // 某个哈希槽（链）上的元素数量增加到此值后，这些元素进入波动期，即将从链表转换为红黑树
    
    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * The value should be at least 4 * TREEIFY_THRESHOLD to avoid
     * conflicts between resizing and treeification thresholds.
     */
    // 散列表长度达到64，且某个桶位中的链表长度达到8，才会发生树化
    static final int MIN_TREEIFY_CAPACITY = 64; // 哈希数组的容量至少增加到此值，且满足TREEIFY_THRESHOLD的要求时，将链表转换为红黑树
    
    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     */
    // 反树化阈值：散列表的一个桶中的红黑树元素个数小于6时候，将红黑树转换回链表结构
    static final int UNTREEIFY_THRESHOLD = 6;   // 哈希槽（链）上的红黑树上的元素数量减少到此值时，将红黑树转换为链表
    
    /**
     * Minimum number of rebinnings per transfer step. Ranges are
     * subdivided to allow multiple resizer threads.  This value
     * serves as a lower bound to avoid resizers encountering
     * excessive memory contention.  The value should be at least
     * DEFAULT_CAPACITY.
     */
    // 控制线程迁移数据的最小步长(桶位的跨度~)
    private static final int MIN_TRANSFER_STRIDE = 16;
    
    /**
     * The number of bits used for generation stamp in sizeCtl.
     * Must be at least 6 for 32bit arrays.
     */
    // 固定值16，与扩容相关，计算扩容时会根据该属性值生成一个扩容标识戳
    private static final int RESIZE_STAMP_BITS = 16;
    
    /**
     * The maximum number of threads that can help resize.
     * Must fit in 32 - RESIZE_STAMP_BITS bits.
     */
    // (1 << (32 - RESIZE_STAMP_BITS)) - 1 = 65535：1 << 16 -1
    // 表示并发扩容最多容纳的线程数
    private static final int MAX_RESIZERS = (1 << (32 - RESIZE_STAMP_BITS)) - 1;
    
    /**
     * The bit shift for recording size stamp in sizeCtl.
     */
    // 也是扩容相关属性，在扩容分析的时候会用到~
    private static final int RESIZE_STAMP_SHIFT = 32 - RESIZE_STAMP_BITS;
    
    /*
     * Encodings for Node hash fields. See above for explanation.
     */
    // 当node节点的hash值为-1：表示当前节点是FWD(forwarding)节点(已经被迁移的节点)
    static final int MOVED     = -1; // hash for forwarding nodes       // 前向结点
    // 当node节点的hash值为-2：表示当前节点已经树化，且当前节点为TreeBin对象~，TreeBin对象代理操作红黑树
    static final int TREEBIN   = -2; // hash for roots of trees         // 红黑树(头结点)
    // 当node节点的hash值为-3：
    static final int RESERVED  = -3; // hash for transient reservations // 占位结点
    // 0x7fffffff 十六进制转二进制值为：1111111111111111111111111111111（31个1）
    // 作用是将一个二进制负数与1111111111111111111111111111111 进行按位与(&)运算时，会得到一个正数，但不是取绝对值
    static final int HASH_BITS = 0x7fffffff; // usable bits of normal node hash
    
    /** Number of CPUS, to place bounds on some sizings */
    // 虚拟机可用的处理器数量
    static final int NCPU = Runtime.getRuntime().availableProcessors();
    
    
    /* ---------------- Fields -------------- */
    
    /**
     * The array of bins. Lazily initialized upon first insertion.
     * Size is always a power of two. Accessed directly by iterators.
     */
    // 散列表table
    transient volatile Node<K,V>[] table;   // 哈希数组（注：哈希数组的容量跟ConcurrentHashMap可以存储的元素数量不是一回事）
    
    /**
     * The next table to use; non-null only while resizing.
     */
    // 新表的引用：扩容过程中，会将扩容中的新table赋值给nextTable，（保持引用），扩容结束之后，这里就会被设置为NULL
    private transient volatile Node<K,V>[] nextTable;   // 哈希数组扩容时使用的新数组
    
    /**
     * Base counter value, used mainly when there is no contention,
     * but also as a fallback during table initialization
     * races. Updated via CAS.
     */
    // 与LongAdder中的baseCount作用相同: 当未发生线程竞争或当前LongAdder处于加锁状态时，增量会被累加到baseCount
    private transient volatile long baseCount;
    
    /**
     * Table initialization and resizing control.
     * When negative, the table is being initialized or resized: -1 for initialization,
     * else -(1 + the number of active resizing threads).
     * Otherwise, when table is null, holds the initial table size to use upon creation, or 0 for default.
     * After initialization, holds the next element count value upon which to resize the table.
     */
    // 表示散列表table的状态:
    // sizeCtl<0时：
    // 情况一、sizeCtl=-1: 表示当前table正在进行初始化(即，有线程在创建table数组)，当前线程需要自旋等待...
    // 情况二、表示当前table散列表正在进行扩容，高16位表示扩容的标识戳，低16位表示扩容线程数：(1 + nThread) 即，当前参与并发扩容的线程数量。
    // sizeCtl=0时：表示创建table散列表时，使用默认初始容量DEFAULT_CAPACITY=16
    // sizeCtl>0时：
    // 情况一、如果table未初始化，表示初始化大小
    // 情况二、如果table已经初始化，表示下次扩容时，触发条件(阈值)
    private transient volatile int sizeCtl;
    
    /**
     * The next table index (plus one) to split while resizing.
     */
    // 扩容过程中，记录当前进度。所有的线程都需要从transferIndex中分配区间任务，并去执行自己的任务
    private transient volatile int transferIndex;
    
    /**
     * Spinlock (locked via CAS) used when resizing and/or creating CounterCells.
     */
    // LongAdder中，cellsBusy表示对象的加锁状态：
    // 0: 表示当前LongAdder对象处于无锁状态
    // 1: 表示当前LongAdder对象处于加锁状态
    private transient volatile int cellsBusy;
    
    /**
     * Table of counter cells. When non-null, size is a power of 2.
     */
    // LongAdder中的cells数组，当baseCount发生线程竞争后，会创建cells数组，
    // 线程会通过计算hash值，去取到自己的cell，将增量累加到指定的cell中
    // 总数 = sum(cells) + baseCount
    private transient volatile CounterCell[] counterCells;
    
    // views
    private transient KeySetView<K,V> keySet;
    private transient ValuesView<K,V> values;
    private transient EntrySetView<K,V> entrySet;
    
    
    // Unsafe mechanics
    private static final Unsafe U = Unsafe.getUnsafe();
    // 表示sizeCtl属性在ConcurrentHashMap中内存的偏移地址
    private static final long SIZECTL;
    // 表示transferIndex属性在ConcurrentHashMap中内存的偏移地址
    private static final long TRANSFERINDEX;
    // 表示transferIndex属性在ConcurrentHashMap中内存的偏移地址
    private static final long BASECOUNT;
    // 表示cellsBusy属性在ConcurrentHashMap中内存的偏移地址
    private static final long CELLSBUSY;
    // 表示cellsValue属性在ConcurrentHashMap中内存的偏移地址
    private static final long CELLVALUE;
    // 表示数组第一个元素的偏移地址
    private static final int ABASE;
    // 该属性用于数组寻址，请继续往下阅读
    private static final int ASHIFT;
    static {
        SIZECTL = U.objectFieldOffset(ConcurrentHashMap.class, "sizeCtl");
        TRANSFERINDEX = U.objectFieldOffset(ConcurrentHashMap.class, "transferIndex");
        BASECOUNT = U.objectFieldOffset(ConcurrentHashMap.class, "baseCount");
        CELLSBUSY = U.objectFieldOffset(ConcurrentHashMap.class, "cellsBusy");
        CELLVALUE = U.objectFieldOffset(CounterCell.class, "value");
        
        // 寻找Node数组中的元素时约定的起始偏移地址（更像是一个标记）
        ABASE = U.arrayBaseOffset(Node[].class);
        
        // Node数组每个元素所占字节数（必须为2的冪）
        // 表示数组中每一个单元所占用的空间大小，即scale表示Node[]数组中每一个单元所占用的空间
        int scale = U.arrayIndexScale(Node[].class);
        // (scale & (scale - 1)) != 0：判断scale的数值是否是2的次幂数
        // java语言规范中，要求数组中计算出的scale必须为2的次幂数
        // 1 0000 % 0 1111 = 0
        if ((scale & (scale - 1)) != 0) {
            throw new ExceptionInInitializerError("array index scale not a power of two");
        }
        
        // 计算log2(scale)，并向下取整
        // numberOfLeadingZeros(scale) 根据scale，返回当前数值转换为二进制后，从高位到地位开始统计，统计有多少个0连续在一块：eg, 8转换二进制=>1000 则 numberOfLeadingZeros(8)的结果就是28，为什么呢？因为Integer是32位，1000占4位，那么前面就有32-4个0，即连续最长的0的个数为28个
        // 4转换二进制=>100 则 numberOfLeadingZeros(8)的结果就是29
        // ASHIFT = 31 - Integer.numberOfLeadingZeros(4) = 2 那么ASHIFT的作用是什么呢？其实它有数组寻址的一个作用：
        // 拿到下标为5的Node[]数组元素的偏移地址(存储地址)：假设此时 根据scale计算得到的ASHIFT = 2
        // ABASE + (5 << ASHIFT) == ABASE + (5 << 2) == ABASE + 5 * scale，就得到了下标为5的数组元素的偏移地址
        ASHIFT = 31 - Integer.numberOfLeadingZeros(scale);
        
        // Reduce the risk of rare disastrous classloading in first call to
        // LockSupport.park: https://bugs.openjdk.java.net/browse/JDK-8074773
        Class<?> ensureLoaded = LockSupport.class;
        
        // Eager class load observed to help JIT during startup
        ensureLoaded = ReservationNode.class;
    }
    
    
    
    /*▼ 构造器 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Creates a new, empty map with the default initial table size (16).
     */
    public ConcurrentHashMap() {
    }
    
    /**
     * Creates a new, empty map with an initial table size
     * accommodating the specified number of elements without the need
     * to dynamically resize.
     *
     * @param initialCapacity The implementation performs internal
     *                        sizing to accommodate this many elements.
     *
     * @throws IllegalArgumentException if the initial capacity of
     *                                  elements is negative
     */
    public ConcurrentHashMap(int initialCapacity) {
        this(initialCapacity, LOAD_FACTOR, 1);
    }
    
    /**
     * Creates a new, empty map with an initial table size based on
     * the given number of elements ({@code initialCapacity}) and
     * initial table density ({@code loadFactor}).
     *
     * @param initialCapacity the initial capacity. The implementation
     *                        performs internal sizing to accommodate this many elements,
     *                        given the specified load factor.
     * @param loadFactor      the load factor (table density) for
     *                        establishing the initial table size
     *
     * @throws IllegalArgumentException if the initial capacity of
     *                                  elements is negative or the load factor is nonpositive
     * @since 1.6
     */
    public ConcurrentHashMap(int initialCapacity, float loadFactor) {
        this(initialCapacity, loadFactor, 1);
    }
    
    /**
     * Creates a new, empty map with an initial table size based on
     * the given number of elements ({@code initialCapacity}), initial
     * table density ({@code loadFactor}), and number of concurrently
     * updating threads ({@code concurrencyLevel}).
     *
     * @param initialCapacity  the initial capacity. The implementation
     *                         performs internal sizing to accommodate this many elements,
     *                         given the specified load factor.
     * @param loadFactor       the load factor (table density) for
     *                         establishing the initial table size
     * @param concurrencyLevel the estimated number of concurrently
     *                         updating threads. The implementation may use this value as
     *                         a sizing hint.
     *
     * @throws IllegalArgumentException if the initial capacity is
     *                                  negative or the load factor or concurrencyLevel are
     *                                  nonpositive
     */
    public ConcurrentHashMap(int initialCapacity, float loadFactor, int concurrencyLevel) {
        if(!(loadFactor>0.0f) || initialCapacity<0 || concurrencyLevel<=0) {
            throw new IllegalArgumentException();
        }
        
        if(initialCapacity<concurrencyLevel) {  // Use at least as many bins
            initialCapacity = concurrencyLevel;   // as estimated threads
        }
        
        long size = (long) (1.0 + (long) initialCapacity / loadFactor);
        
        this.sizeCtl = (size >= (long) MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : tableSizeFor((int) size);
    }
    
    /**
     * Creates a new map with the same mappings as the given map.
     *
     * @param m the map
     */
    public ConcurrentHashMap(Map<? extends K, ? extends V> m) {
        //e-hentai.org
        this.sizeCtl = DEFAULT_CAPACITY;
        putAll(m);
    }
    
    /*▲ 构造器 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 存值 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Maps the specified key to the specified value in this table.
     * Neither the key nor the value can be null.
     *
     * <p>The value can be retrieved by calling the {@code get} method
     * with a key that is equal to the original key.
     *
     * @param key   key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     *
     * @return the previous value associated with {@code key}, or
     * {@code null} if there was no mapping for {@code key}
     *
     * @throws NullPointerException if the specified key or value is null
     */
    // 将指定的元素（key-value）存入当前map，并返回旧值，允许覆盖
    public V put(K key, V value) {
        return putVal(key, value, false);
    }
    
    /**
     * {@inheritDoc}
     *
     * @return the previous value associated with the specified key,
     * or {@code null} if there was no mapping for the key
     *
     * @throws NullPointerException if the specified key or value is null
     */
    // 将指定的元素（key-value）存入当前map，并返回旧值，不允许覆盖
    public V putIfAbsent(K key, V value) {
        return putVal(key, value, true);
    }
    
    /**
     * Copies all of the mappings from the specified map to this one.
     * These mappings replace any mappings that this map had for any of the
     * keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     */
    // 将指定Map中的元素存入到当前Map（允许覆盖）
    public void putAll(Map<? extends K, ? extends V> m) {
        tryPresize(m.size());
        
        for(Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
            putVal(e.getKey(), e.getValue(), false);
        }
    }
    
    /*▲ 存值 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 取值 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code key.equals(k)},
     * then this method returns {@code v}; otherwise it returns
     * {@code null}.  (There can be at most one such mapping.)
     *
     * @throws NullPointerException if the specified key is null
     */
    // 根据指定的key获取对应的value，如果不存在，则返回null
    public V get(Object key) {
        Node<K, V>[] tab; // tab 引用map.table
        Node<K, V> e;     // e 当前元素(用于循环遍历)
        Node<K, V> p;     // p 目标节点
        int n, eh;  // n table数组长度 // eh 当前元素hash
        K ek; // ek 当前元素key

        // 根据key.hashCode()计算hash: 扰动运算后得到得到更散列的hash值
        int h = spread(key.hashCode());
        // --------------------------------------------------------------------------------
        // CASE1:
        // 如果元素所在的桶存在且里面有元素
        // 条件一：(tab = table) != null
        // 		true -> 表示已经put过数据，并且map内部的table也已经初始化完毕
        // 		false -> 表示创建完map后，并没有put过数据，map内部的table是延迟初始化的，只有第一次写数据时会触发初始化创建table逻辑
        // 条件二：(n = tab.length) > 0 如果为 true-> 表示table已经初始化
        // 条件三：(e = tabAt(tab, (n - 1) & h)) != null
        // 		true -> 当前key寻址的桶位有值
        // 		false -> 当前key寻址的桶位中是null，是null直接返回null
        if ((tab = table) != null
                && (n = tab.length) > 0
                && (e = tabAt(tab, (n - 1) & h)) != null) {
            // 进入if代码块内部的前置条件：当前桶位有数据

            // 如果第一个元素就是要找的元素，则直接返回
            // 对比头结点hash与查询key的hash是否一致
            // 条件成立：说明头结点与查询Key的hash值完全一致
            if ((eh = e.hash) == h) {
                // 完全比对 查询key 和 头结点的key
                // 条件成立：说明头结点就是查询数据
                if ((ek = e.key) == key
                        || (ek != null && key.equals(ek))) {
                    // 当e的hash值以及e对应的key都匹配目标元素时，则找到了，直接返回~
                    return e.val;
                }
            }
            // --------------------------------------------------------------------------------
            // CASE2: eh < 0
            // 条件成立：即，hash小于0 分2种情况，是树或者正在扩容,需要借助find方法寻找元素，find的寻找方式依据Node的不同子类有不同的实现方式:
            // 情况一：eh=-1 是fwd结点 -> 说明当前table正在扩容，且当前查询的这个桶位的数据已经被迁移走了，需要借助fwd结点的内部方法find去查询
            // 情况二：eh=-2 是TreeBin节点 -> 需要使用TreeBin 提供的find方法查询。
            else if(eh < 0) {
                return (p = e.find(h, key)) != null ? p.val : null;
            }
            // --------------------------------------------------------------------------------
            // CASE3: 前提条件 -> CASE1和CASE2条件不满足！
            // 说明是当前桶位已经形成链表的这种情况: 遍历整个链表寻找元素
            while ((e = e.next) != null) {
                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                    return e.val;
                }
            }
        }
        
        return null;
    }
    
    /**
     * Returns the value to which the specified key is mapped, or the
     * given default value if this map contains no mapping for the
     * key.
     *
     * @param key          the key whose associated value is to be returned
     * @param defaultValue the value to return if this map contains
     *                     no mapping for the given key
     *
     * @return the mapping for the key, if present; else the default value
     *
     * @throws NullPointerException if the specified key is null
     */
    // 根据指定的key获取对应的value，如果不存在，则返回指定的默认值defaultValue
    public V getOrDefault(Object key, V defaultValue) {
        V v = get(key);
        return v == null ? defaultValue : v;
    }
    
    /*▲ 取值 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 移除 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Removes the key (and its corresponding value) from this map.
     * This method does nothing if the key is not in the map.
     *
     * @param key the key that needs to be removed
     *
     * @return the previous value associated with {@code key}, or
     * {@code null} if there was no mapping for {@code key}
     *
     * @throws NullPointerException if the specified key is null
     */
    // 移除拥有指定key的元素，并返回刚刚移除的元素的值
    public V remove(Object key) {
        // 调用替换节点方法
        return replaceNode(key, null, null);
    }
    
    /**
     * {@inheritDoc}
     *
     * @throws NullPointerException if the specified key is null
     */
    // 移除拥有指定key和value的元素，返回值表示是否移除成功
    public boolean remove(Object key, Object value) {
        if(key == null) {
            throw new NullPointerException();
        }
        
        return value != null && replaceNode(key, null, value) != null;
    }
    
    
    /**
     * Removes all of the mappings from this map.
     */
    // 清空当前Map中所有元素
    public void clear() {
        long delta = 0L; // negative number of deletions
        int i = 0;
        
        Node<K, V>[] tab = table;
        
        while(tab != null && i<tab.length) {
            int fh;
            Node<K, V> f = tabAt(tab, i);
            
            if(f == null) {
                ++i;
            } else if((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
                i = 0; // restart
            } else {
                synchronized(f) {
                    if(tabAt(tab, i) == f) {
                        Node<K, V> p = (fh >= 0 ? f : (f instanceof TreeBin) ? ((TreeBin<K, V>) f).first : null);
                        while(p != null) {
                            --delta;
                            p = p.next;
                        }
                        
                        // 设置tab[i]为null
                        setTabAt(tab, i++, null);
                    }
                }
            }
        }
        
        if(delta != 0L) {
            addCount(delta, -1);
        }
    }
    
    /*▲ 移除 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 替换 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * {@inheritDoc}
     *
     * @return the previous value associated with the specified key,
     * or {@code null} if there was no mapping for the key
     *
     * @throws NullPointerException if the specified key or value is null
     */
    // 将拥有指定key的元素的值替换为newValue，并返回刚刚替换的元素的值（替换失败返回null）
    public V replace(K key, V newValue) {
        if(key == null || newValue == null) {
            throw new NullPointerException();
        }
        
        return replaceNode(key, newValue, null);
    }
    
    /**
     * {@inheritDoc}
     *
     * @throws NullPointerException if any of the arguments are null
     */
    // 将拥有指定key和oldValue的元素的值替换为newValue，返回值表示是否成功替换
    public boolean replace(K key, V oldValue, V newValue) {
        if(key == null || oldValue == null || newValue == null) {
            throw new NullPointerException();
        }
        
        return replaceNode(key, newValue, oldValue) != null;
    }
    
    // 替换当前Map中的所有元素，替换策略由function决定，function的入参是元素的key和value，出参作为新值
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if(function == null) {
            throw new NullPointerException();
        }
        
        Node<K, V>[] t;
        
        if((t = table) != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            
            for(Node<K, V> p; (p = it.advance()) != null; ) {
                V oldValue = p.val;
                
                for(K key = p.key; ; ) {
                    V newValue = function.apply(key, oldValue);
                    
                    if(newValue == null) {
                        throw new NullPointerException();
                    }
                    
                    if(replaceNode(key, newValue, oldValue) != null || (oldValue = get(key)) == null) {
                        break;
                    }
                }
            }
        }
    }
    
    /*▲ 替换 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 包含查询 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Tests if the specified object is a key in this table.
     *
     * @param key possible key
     *
     * @return {@code true} if and only if the specified object
     * is a key in this table, as determined by the
     * {@code equals} method; {@code false} otherwise
     *
     * @throws NullPointerException if the specified key is null
     */
    // 判断Map中是否存在指定key的元素
    public boolean containsKey(Object key) {
        return get(key) != null;
    }
    
    /**
     * Returns {@code true} if this map maps one or more keys to the
     * specified value. Note: This method may require a full traversal
     * of the map, and is much slower than method {@code containsKey}.
     *
     * @param value value whose presence in this map is to be tested
     *
     * @return {@code true} if this map maps one or more keys to the
     * specified value
     *
     * @throws NullPointerException if the specified value is null
     */
    // 判断Map中是否存在指定value的元素
    public boolean containsValue(Object value) {
        if(value == null) {
            throw new NullPointerException();
        }
        
        Node<K, V>[] t = table;
        if(t != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            
            for(Node<K, V> p; (p = it.advance()) != null; ) {
                V v = p.val;
                if(v == value || (v != null && value.equals(v))) {
                    return true;
                }
            }
        }
        
        return false;
    }
    
    /**
     * Tests if some key maps into the specified value in this table.
     *
     * <p>Note that this method is identical in functionality to
     * {@link #containsValue(Object)}, and exists solely to ensure
     * full compatibility with class {@link java.util.Hashtable},
     * which supported this method prior to introduction of the
     * Java Collections Framework.
     *
     * @param value a value to search for
     *
     * @return {@code true} if and only if some key maps to the
     * {@code value} argument in this table as
     * determined by the {@code equals} method;
     * {@code false} otherwise
     *
     * @throws NullPointerException if the specified value is null
     */
    // 判断Map中是否存在指定value的元素
    public boolean contains(Object value) {
        return containsValue(value);
    }
    
    /*▲ 包含查询 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 视图 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa. The set supports element
     * removal, which removes the corresponding mapping from this map,
     * via the {@code Iterator.remove}, {@code Set.remove},
     * {@code removeAll}, {@code retainAll}, and {@code clear}
     * operations.  It does not support the {@code add} or
     * {@code addAll} operations.
     *
     * <p>The view's iterators and spliterators are
     * <a href="package-summary.html#Weakly"><i>weakly consistent</i></a>.
     *
     * <p>The view's {@code spliterator} reports {@link Spliterator#CONCURRENT},
     * {@link Spliterator#DISTINCT}, and {@link Spliterator#NONNULL}.
     *
     * @return the set view
     */
    // 获取Map中key的集合
    public KeySetView<K, V> keySet() {
        KeySetView<K, V> ks;
        if((ks = keySet) != null) {
            return ks;
        }
        return keySet = new KeySetView<K, V>(this, null);
    }
    
    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  The collection
     * supports element removal, which removes the corresponding
     * mapping from this map, via the {@code Iterator.remove},
     * {@code Collection.remove}, {@code removeAll},
     * {@code retainAll}, and {@code clear} operations.  It does not
     * support the {@code add} or {@code addAll} operations.
     *
     * <p>The view's iterators and spliterators are
     * <a href="package-summary.html#Weakly"><i>weakly consistent</i></a>.
     *
     * <p>The view's {@code spliterator} reports {@link Spliterator#CONCURRENT}
     * and {@link Spliterator#NONNULL}.
     *
     * @return the collection view
     */
    // 获取Map中value的集合
    public Collection<V> values() {
        ValuesView<K, V> vs;
        if((vs = values) != null) {
            return vs;
        }
        return values = new ValuesView<K, V>(this);
    }
    
    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  The set supports element
     * removal, which removes the corresponding mapping from the map,
     * via the {@code Iterator.remove}, {@code Set.remove},
     * {@code removeAll}, {@code retainAll}, and {@code clear}
     * operations.
     *
     * <p>The view's iterators and spliterators are
     * <a href="package-summary.html#Weakly"><i>weakly consistent</i></a>.
     *
     * <p>The view's {@code spliterator} reports {@link Spliterator#CONCURRENT},
     * {@link Spliterator#DISTINCT}, and {@link Spliterator#NONNULL}.
     *
     * @return the set view
     */
    // 获取Map中key-value对的集合
    public Set<Map.Entry<K, V>> entrySet() {
        EntrySetView<K, V> es;
        if((es = entrySet) != null) {
            return es;
        }
        return entrySet = new EntrySetView<K, V>(this);
    }
    
    /*▲ 视图 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 遍历 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    // 遍历ConcurrentHashMap中的元素，并对其应用action操作，action的入参是元素的key和value
    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) {
            throw new NullPointerException();
        }
        
        Node<K,V>[] t;
        if ((t = table) != null) {
            Traverser<K,V> it = new Traverser<K,V>(t, t.length, 0, t.length);
            for (Node<K,V> p; (p = it.advance()) != null; ) {
                action.accept(p.key, p.val);
            }
        }
    }
    
    /**
     * Returns an enumeration of the keys in this table.
     *
     * @return an enumeration of the keys in this table
     *
     * @see #keySet()
     */
    // 返回关于键集的枚举
    public Enumeration<K> keys() {
        Node<K, V>[] t;
        int f = (t = table) == null ? 0 : t.length;
        return new KeyIterator<K, V>(t, f, 0, f, this);
    }
    
    /**
     * Returns an enumeration of the values in this table.
     *
     * @return an enumeration of the values in this table
     *
     * @see #values()
     */
    // 返回关于值集的枚举
    public Enumeration<V> elements() {
        Node<K, V>[] t;
        int f = (t = table) == null ? 0 : t.length;
        return new ValueIterator<K, V>(t, f, 0, f, this);
    }
    
    /*▲ 遍历 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 重新映射 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * If the specified key is not already associated with a
     * (non-null) value, associates it with the given value.
     * Otherwise, replaces the value with the results of the given
     * remapping function, or removes if {@code null}. The entire
     * method invocation is performed atomically.  Some attempted
     * update operations on this map by other threads may be blocked
     * while computation is in progress, so the computation should be
     * short and simple, and must not attempt to update any other
     * mappings of this Map.
     *
     * @param key               key with which the specified value is to be associated
     * @param bakValue          the value to use if absent
     * @param remappingFunction the function to recompute a value if present
     *
     * @return the new value associated with the specified key, or null if none
     *
     * @throws NullPointerException if the specified key or the
     *                              remappingFunction is null
     * @throws RuntimeException     or Error if the remappingFunction does so,
     *                              in which case the mapping is unchanged
     */
    /*
     * 插入/删除/替换操作，返回新值（可能为null）
     * 此方法的主要意图：使用备用value和旧value创造的新value来更新旧value
     *
     * 注：以下流程图中，涉及到判断(◇)时，纵向代表【是】，横向代表【否】。此外，使用★代表计算。
     *
     *  ●查找同位元素●
     *      |
     *      ↓
     * ◇存在同位元素◇    --→ ★新value=备用value★ --→ ■如果新value不为null，【插入】新value■
     *      | 是         否
     *      ↓
     * ★新value=(旧value, 备用value)★
     *      |
     *      ↓
     * ◇新value不为null◇ --→ ■【删除】同位元素■
     *      | 是          否
     *      ↓
     * ■新value【替换】旧value■
     */
    public V merge(K key, V bakValue, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if(key == null || bakValue == null || remappingFunction == null) {
            throw new NullPointerException();
        }
        
        int h = spread(key.hashCode());
        
        V newValue = null;
        int delta = 0;
        int binCount = 0;
        Node<K, V>[] tab = table;
        for(; ; ) {
            Node<K, V> f;
            int n, i, fh;
            if(tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if((f = tabAt(tab, i = (n - 1) & h)) == null) {
                // 当做新元素插入
                Node<K, V> x = new Node<>(h, key, bakValue);
                // 原子地更新tab[i]为x
                if(casTabAt(tab, i, null, x)) {
                    delta = 1;
                    newValue = bakValue;
                    break;
                }
            } else if((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
            } else {
                synchronized(f) {
                    if(tabAt(tab, i) == f) {
                        if(fh >= 0) {
                            binCount = 1;
                            
                            for(Node<K, V> e = f, pred = null; ; ++binCount) {
                                K ek;
                                
                                // 找到了同位元素
                                if(e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    // 生成新值
                                    newValue = remappingFunction.apply(e.val, bakValue);
                                    
                                    // 新值不为空，则替换
                                    if(newValue != null) {
                                        e.val = newValue;
                                        
                                        // 新值为空，则移除旧元素
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        
                                        if(pred != null) {
                                            pred.next = en;
                                        } else {
                                            // 设置tab[i]为en
                                            setTabAt(tab, i, en);
                                        }
                                    }
                                    
                                    break;
                                }
                                
                                pred = e;
                                
                                // 当做新元素插入
                                if((e = e.next) == null) {
                                    delta = 1;
                                    newValue = bakValue;
                                    pred.next = new Node<K, V>(h, key, newValue);
                                    break;
                                }
                            }
                        } else if(f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r = t.root;
                            TreeNode<K, V> p = (r == null) ? null : r.findTreeNode(h, key, null);
                            newValue = (p == null) ? bakValue : remappingFunction.apply(p.val, bakValue);
                            if(newValue != null) {
                                if(p != null) {
                                    p.val = newValue;
                                } else {
                                    delta = 1;
                                    t.putTreeVal(h, key, newValue);
                                }
                            } else if(p != null) {
                                delta = -1;
                                
                                if(t.removeTreeNode(p)) {
                                    Node<K, V> x = untreeify(t.first);
                                    // 设置tab[i]为x
                                    setTabAt(tab, i, x);
                                }
                            }
                        } else if(f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                
                if(binCount != 0) {
                    if(binCount >= TREEIFY_THRESHOLD) {
                        treeifyBin(tab, i);
                    }
                    break;
                }
            }
        }// for(; ; )
        
        if(delta != 0) {
            addCount(delta, binCount);
        }
        
        return newValue;
    }
    
    /**
     * Attempts to compute a mapping for the specified key and its
     * current mapped value (or {@code null} if there is no current
     * mapping). The entire method invocation is performed atomically.
     * Some attempted update operations on this map by other threads
     * may be blocked while computation is in progress, so the
     * computation should be short and simple, and must not attempt to
     * update any other mappings of this Map.
     *
     * @param key               key with which the specified value is to be associated
     * @param remappingFunction the function to compute a value
     *
     * @return the new value associated with the specified key, or null if none
     *
     * @throws NullPointerException  if the specified key or remappingFunction
     *                               is null
     * @throws IllegalStateException if the computation detectably
     *                               attempts a recursive update to this map that would
     *                               otherwise never complete
     * @throws RuntimeException      or Error if the remappingFunction does so,
     *                               in which case the mapping is unchanged
     */
    /*
     * 插入/删除/替换操作，返回新值（可能为null）
     * 此方法的主要意图：使用key和旧value创造的新value来更新旧value
     *
     * 注：以下流程图中，涉及到判断(◇)时，纵向代表【是】，横向代表【否】。此外，使用★代表计算。
     *
     *  ●查找同位元素●
     *      |
     *      ↓
     * ◇存在同位元素◇     --→ ★新value=(key, null)★
     *      | 是          否　           |
     *      ↓ 　　　                     |
     * ★新value=(key, 旧value)★        |
     *      ├---------------------------┘
     *      ↓
     * ◇新value不为null◇ --→ ■如果存在同位元素，则【删除】同位元素■
     *      | 是          否
     *      ↓
     * ■  存在同位元素，则新value【替换】旧value■
     * ■不存在同位元素，则【插入】新value       ■
     */
    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if(key == null || remappingFunction == null) {
            throw new NullPointerException();
        }
        
        int h = spread(key.hashCode());
        
        V newValue = null;
        int delta = 0;
        int binCount = 0;
        
        for(Node<K, V>[] tab = table; ; ) {
            Node<K, V> f;
            int n, i, fh;
            
            if(tab == null || (n = tab.length) == 0) {
                tab = initTable();
                
            } else if((f = tabAt(tab, i = (n - 1) & h)) == null) {
                // 设置一个占位结点
                Node<K, V> x = new ReservationNode<>();
                
                synchronized(x) {
                    // 原子地更新tab[i]为x
                    if(casTabAt(tab, i, null, x)) {
                        binCount = 1;
                        Node<K, V> node = null;
                        try {
                            newValue = remappingFunction.apply(key, null);
                            
                            if(newValue != null) {
                                delta = 1;
                                node = new Node<K, V>(h, key, newValue);
                            }
                        } finally {
                            // 设置tab[i]为node
                            setTabAt(tab, i, node);
                        }
                    }
                }
                
                if(binCount != 0) {
                    break;
                }
            } else if((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
            } else {
                synchronized(f) {
                    if(tabAt(tab, i) == f) {
                        if(fh >= 0) {
                            binCount = 1;
                            
                            for(Node<K, V> e = f, pred = null; ; ++binCount) {
                                K ek;
                                
                                // 找到了同位元素
                                if(e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    newValue = remappingFunction.apply(key, e.val);
                                    
                                    if(newValue != null) {
                                        e.val = newValue;
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        if(pred != null) {
                                            pred.next = en;
                                        } else {
                                            // 设置tab[i]为en
                                            setTabAt(tab, i, en);
                                        }
                                    }
                                    break;
                                }
                                
                                pred = e;
                                
                                if((e = e.next) == null) {
                                    newValue = remappingFunction.apply(key, null);
                                    
                                    if(newValue != null) {
                                        if(pred.next != null) {
                                            throw new IllegalStateException("Recursive update");
                                        }
                                        delta = 1;
                                        pred.next = new Node<K, V>(h, key, newValue);
                                    }
                                    
                                    break;
                                }
                            }
                        } else if(f instanceof TreeBin) {
                            binCount = 1;
                            
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            
                            if((r = t.root) != null) {
                                p = r.findTreeNode(h, key, null);
                            } else {
                                p = null;
                            }
                            
                            V pv = (p == null) ? null : p.val;
                            
                            newValue = remappingFunction.apply(key, pv);
                            
                            if(newValue != null) {
                                if(p != null) {
                                    p.val = newValue;
                                } else {
                                    delta = 1;
                                    t.putTreeVal(h, key, newValue);
                                }
                            } else if(p != null) {
                                delta = -1;
                                if(t.removeTreeNode(p)) {
                                    Node<K, V> x = untreeify(t.first);
                                    // 设置tab[i]为x
                                    setTabAt(tab, i, x);
                                }
                            }
                        } else if(f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                
                if(binCount != 0) {
                    if(binCount >= TREEIFY_THRESHOLD) {
                        treeifyBin(tab, i);
                    }
                    
                    break;
                }
            }
        }
        
        if(delta != 0) {
            addCount(delta, binCount);
        }
        
        return newValue;
    }
    
    /**
     * If the value for the specified key is present, attempts to
     * compute a new mapping given the key and its current mapped
     * value.  The entire method invocation is performed atomically.
     * Some attempted update operations on this map by other threads
     * may be blocked while computation is in progress, so the
     * computation should be short and simple, and must not attempt to
     * update any other mappings of this map.
     *
     * @param key               key with which a value may be associated
     * @param remappingFunction the function to compute a value
     *
     * @return the new value associated with the specified key, or null if none
     *
     * @throws NullPointerException  if the specified key or remappingFunction
     *                               is null
     * @throws IllegalStateException if the computation detectably
     *                               attempts a recursive update to this map that would
     *                               otherwise never complete
     * @throws RuntimeException      or Error if the remappingFunction does so,
     *                               in which case the mapping is unchanged
     */
    /*
     * 删除/替换操作，返回新值（可能为null）
     * 此方法的主要意图：存在同位元素时，使用key和旧value创造的新value来更新旧value
     *
     * 注：以下流程图中，涉及到判断(◇)时，纵向代表【是】，横向代表【否】。此外，使用★代表计算。
     *
     *  ●查找同位元素●
     *      |
     *      ↓
     * ◇存在同位元素◇
     *      | 是
     *      ↓
     * ★新value=(key, 旧value)★
     *      |
     *      ↓
     * ◇新value不为null◇ --→ ■【删除】同位元素■
     *      | 是          否
     *      ↓
     * ■新value【替换】旧value■
     */
    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if(key == null || remappingFunction == null) {
            throw new NullPointerException();
        }
        
        int h = spread(key.hashCode());
        
        V newValue = null;
        int delta = 0;
        int binCount = 0;
        for(Node<K, V>[] tab = table; ; ) {
            Node<K, V> f;
            int n, i, fh;
            
            if(tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if((f = tabAt(tab, i = (n - 1) & h)) == null) {
                break;
            } else if((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
            } else {
                synchronized(f) {
                    if(tabAt(tab, i) == f) {
                        if(fh >= 0) {
                            binCount = 1;
                            for(Node<K, V> e = f, pred = null; ; ++binCount) {
                                K ek;
                                
                                // 找到了同位元素
                                if(e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    newValue = remappingFunction.apply(key, e.val);
                                    
                                    if(newValue != null) {
                                        e.val = newValue;
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        if(pred != null) {
                                            pred.next = en;
                                        } else {
                                            // 设置tab[i]为en
                                            setTabAt(tab, i, en);
                                        }
                                    }
                                    break;
                                }
                                
                                pred = e;
                                
                                if((e = e.next) == null) {
                                    break;
                                }
                            }
                        } else if(f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            if((r = t.root) != null && (p = r.findTreeNode(h, key, null)) != null) {
                                newValue = remappingFunction.apply(key, p.val);
                                
                                if(newValue != null) {
                                    p.val = newValue;
                                } else {
                                    delta = -1;
                                    if(t.removeTreeNode(p)) {
                                        Node<K, V> x = untreeify(t.first);
                                        // 设置tab[i]为x
                                        setTabAt(tab, i, x);
                                    }
                                }
                            }
                        } else if(f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                
                if(binCount != 0) {
                    break;
                }
            }
        }
        
        if(delta != 0) {
            addCount(delta, binCount);
        }
        
        return newValue;
    }
    
    /**
     * If the specified key is not already associated with a value,
     * attempts to compute its value using the given mapping function
     * and enters it into this map unless {@code null}.  The entire
     * method invocation is performed atomically, so the function is
     * applied at most once per key.  Some attempted update operations
     * on this map by other threads may be blocked while computation
     * is in progress, so the computation should be short and simple,
     * and must not attempt to update any other mappings of this map.
     *
     * @param key             key with which the specified value is to be associated
     * @param mappingFunction the function to compute a value
     *
     * @return the current (existing or computed) value associated with
     * the specified key, or null if the computed value is null
     *
     * @throws NullPointerException  if the specified key or mappingFunction
     *                               is null
     * @throws IllegalStateException if the computation detectably
     *                               attempts a recursive update to this map that would
     *                               otherwise never complete
     * @throws RuntimeException      or Error if the mappingFunction does so,
     *                               in which case the mapping is left unestablished
     */
    /*
     * 插入操作，返回新值（可能为null）
     * 此方法的主要意图：不存在同位元素时，使用key创造的新value来更新旧value。如果同位元素存在，则直接返回旧值。
     *
     * 注：以下流程图中，涉及到判断(◇)时，纵向代表【是】，横向代表【否】。此外，使用★代表计算。
     *
     *  ●查找同位元素●
     *      |
     *      ↓
     * ◇存在同位元素◇ --→ ★新value=(key)★
     *                否         |
     *                　         ↓
     *                　  ◇新value不为null◇
     *                　         |
     *                　         ↓
     *                　  ■不存在同位元素，则【插入】新value■
     */
    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if(key == null || mappingFunction == null) {
            throw new NullPointerException();
        }
        
        int h = spread(key.hashCode());
        
        V newValue = null;
        int binCount = 0;
        for(Node<K, V>[] tab = table; ; ) {
            Node<K, V> f;
            int n, i, fh;
            K fk;
            V fv;
            
            if(tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if((f = tabAt(tab, i = (n - 1) & h)) == null) {
                Node<K, V> x = new ReservationNode<>();
                
                synchronized(x) {
                    // 原子地更新tab[i]为x
                    if(casTabAt(tab, i, null, x)) {
                        binCount = 1;
                        Node<K, V> node = null;
                        try {
                            newValue = mappingFunction.apply(key);
                            
                            if(newValue != null) {
                                node = new Node<K, V>(h, key, newValue);
                            }
                        } finally {
                            // 设置tab[i]为node
                            setTabAt(tab, i, node);
                        }
                    }
                }
                if(binCount != 0) {
                    break;
                }
            } else if((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
            } else if(fh == h    // check first node without acquiring lock
                && ((fk = f.key) == key || (fk != null && key.equals(fk))) && (fv = f.val) != null) {
                return fv;
            } else {
                boolean added = false;
                synchronized(f) {
                    if(tabAt(tab, i) == f) {
                        if(fh >= 0) {
                            binCount = 1;
                            for(Node<K, V> e = f; ; ++binCount) {
                                K ek;
                                if(e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    newValue = e.val;
                                    break;
                                }
                                
                                Node<K, V> pred = e;
                                
                                if((e = e.next) == null) {
                                    newValue = mappingFunction.apply(key);
                                    
                                    if(newValue != null) {
                                        if(pred.next != null) {
                                            throw new IllegalStateException("Recursive update");
                                        }
                                        added = true;
                                        pred.next = new Node<K, V>(h, key, newValue);
                                    }
                                    break;
                                }
                            }
                        } else if(f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            if((r = t.root) != null && (p = r.findTreeNode(h, key, null)) != null) {
                                newValue = p.val;
                            } else if((newValue = mappingFunction.apply(key)) != null) {
                                added = true;
                                t.putTreeVal(h, key, newValue);
                            }
                        } else if(f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                
                if(binCount != 0) {
                    if(binCount >= TREEIFY_THRESHOLD) {
                        treeifyBin(tab, i);
                    }
                    
                    if(!added) {
                        return newValue;
                    }
                    
                    break;
                }
            }
        }
        
        if(newValue != null) {
            addCount(1L, binCount);
        }
        
        return newValue;
    }
    
    /*▲ 重新映射 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 杂项 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * {@inheritDoc}
     */
    // 获取当前Map中的元素数量
    public int size() {
        long n = sumCount();
        return ((n<0L) ? 0 : (n>(long) Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int) n);
    }
    
    /**
     * {@inheritDoc}
     */
    // 判断当前Map是否为空集
    public boolean isEmpty() {
        return sumCount()<=0L; // ignore transient negative values
    }
    
    /*▲ 杂项 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 并行操作 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    /**
     * Performs the given action for each key.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param action               the action
     *
     * @since 1.8
     */
    public void forEachKey(long parallelismThreshold, Consumer<? super K> action) {
        if(action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachKeyTask<K, V>(null, batch, 0, 0, table, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param action               the action
     *
     * @since 1.8
     */
    public void forEachValue(long parallelismThreshold, Consumer<? super V> action) {
        if(action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachValueTask<K, V>(null, batch, 0, 0, table, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each entry.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param action               the action
     *
     * @since 1.8
     */
    public void forEachEntry(long parallelismThreshold, Consumer<? super Map.Entry<K, V>> action) {
        if(action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachEntryTask<K, V>(null, batch, 0, 0, table, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each (key, value).
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param action               the action
     *
     * @since 1.8
     */
    public void forEach(long parallelismThreshold, BiConsumer<? super K, ? super V> action) {
        if(action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachMappingTask<>(null, batch, 0, 0, table, action);
        
        task.invoke();
    }
    
    
    
    /**
     * Performs the given action for each non-null transformation
     * of each key.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case the action is not applied)
     * @param action               the action
     * @param <U>                  the return type of the transformer
     *
     * @since 1.8
     */
    public <U> void forEachKey(long parallelismThreshold, Function<? super K, ? extends U> transformer, Consumer<? super U> action) {
        if(transformer == null || action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachTransformedKeyTask<K, V, U>(null, batch, 0, 0, table, transformer, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each non-null transformation
     * of each value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case the action is not applied)
     * @param action               the action
     * @param <U>                  the return type of the transformer
     *
     * @since 1.8
     */
    public <U> void forEachValue(long parallelismThreshold, Function<? super V, ? extends U> transformer, Consumer<? super U> action) {
        if(transformer == null || action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachTransformedValueTask<K, V, U>(null, batch, 0, 0, table, transformer, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each non-null transformation
     * of each entry.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case the action is not applied)
     * @param action               the action
     * @param <U>                  the return type of the transformer
     *
     * @since 1.8
     */
    public <U> void forEachEntry(long parallelismThreshold, Function<Map.Entry<K, V>, ? extends U> transformer, Consumer<? super U> action) {
        if(transformer == null || action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachTransformedEntryTask<K, V, U>(null, batch, 0, 0, table, transformer, action);
        
        task.invoke();
    }
    
    /**
     * Performs the given action for each non-null transformation
     * of each (key, value).
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case the action is not applied)
     * @param action               the action
     * @param <U>                  the return type of the transformer
     *
     * @since 1.8
     */
    public <U> void forEach(long parallelismThreshold, BiFunction<? super K, ? super V, ? extends U> transformer, Consumer<? super U> action) {
        if(transformer == null || action == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Void> task = new ForEachTransformedMappingTask<K, V, U>(null, batch, 0, 0, table, transformer, action);
        
        task.invoke();
    }
    
    
    
    /**
     * Returns a non-null result from applying the given search
     * function on each key, or null if none. Upon success,
     * further element processing is suppressed and the results of
     * any other parallel invocations of the search function are
     * ignored.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param searchFunction       a function returning a non-null
     *                             result on success, else null
     * @param <U>                  the return type of the search function
     *
     * @return a non-null result from applying the given search
     * function on each key, or null if none
     *
     * @since 1.8
     */
    public <U> U searchKeys(long parallelismThreshold, Function<? super K, ? extends U> searchFunction) {
        if(searchFunction == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new SearchKeysTask<K, V, U>(null, batch, 0, 0, table, searchFunction, new AtomicReference<U>());
        
        return task.invoke();
    }
    
    /**
     * Returns a non-null result from applying the given search
     * function on each value, or null if none.  Upon success,
     * further element processing is suppressed and the results of
     * any other parallel invocations of the search function are
     * ignored.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param searchFunction       a function returning a non-null
     *                             result on success, else null
     * @param <U>                  the return type of the search function
     *
     * @return a non-null result from applying the given search
     * function on each value, or null if none
     *
     * @since 1.8
     */
    public <U> U searchValues(long parallelismThreshold, Function<? super V, ? extends U> searchFunction) {
        if(searchFunction == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new SearchValuesTask<K, V, U>(null, batch, 0, 0, table, searchFunction, new AtomicReference<U>());
        
        return task.invoke();
    }
    
    /**
     * Returns a non-null result from applying the given search
     * function on each entry, or null if none.  Upon success,
     * further element processing is suppressed and the results of
     * any other parallel invocations of the search function are
     * ignored.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param searchFunction       a function returning a non-null
     *                             result on success, else null
     * @param <U>                  the return type of the search function
     *
     * @return a non-null result from applying the given search
     * function on each entry, or null if none
     *
     * @since 1.8
     */
    public <U> U searchEntries(long parallelismThreshold, Function<Map.Entry<K, V>, ? extends U> searchFunction) {
        if(searchFunction == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new SearchEntriesTask<K, V, U>(null, batch, 0, 0, table, searchFunction, new AtomicReference<U>());
        
        return task.invoke();
    }
    
    /**
     * Returns a non-null result from applying the given search
     * function on each (key, value), or null if none.  Upon
     * success, further element processing is suppressed and the
     * results of any other parallel invocations of the search
     * function are ignored.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param searchFunction       a function returning a non-null
     *                             result on success, else null
     * @param <U>                  the return type of the search function
     *
     * @return a non-null result from applying the given search
     * function on each (key, value), or null if none
     *
     * @since 1.8
     */
    public <U> U search(long parallelismThreshold, BiFunction<? super K, ? super V, ? extends U> searchFunction) {
        if(searchFunction == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new SearchMappingsTask<K, V, U>(null, batch, 0, 0, table, searchFunction, new AtomicReference<U>());
        
        return task.invoke();
    }
    
    
    
    /**
     * Returns the result of accumulating all keys using the given
     * reducer to combine values, or null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating all keys using the given
     * reducer to combine values, or null if none
     *
     * @since 1.8
     */
    public K reduceKeys(long parallelismThreshold, BiFunction<? super K, ? super K, ? extends K> reducer) {
        if(reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<K> task = new ReduceKeysTask<K, V>(null, batch, 0, 0, table, null, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating all values using the
     * given reducer to combine values, or null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating all values
     *
     * @since 1.8
     */
    public V reduceValues(long parallelismThreshold, BiFunction<? super V, ? super V, ? extends V> reducer) {
        if(reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<V> task = new ReduceValuesTask<K, V>(null, batch, 0, 0, table, null, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating all entries using the
     * given reducer to combine values, or null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating all entries
     *
     * @since 1.8
     */
    public Map.Entry<K, V> reduceEntries(long parallelismThreshold, BiFunction<Map.Entry<K, V>, Map.Entry<K, V>, ? extends Map.Entry<K, V>> reducer) {
        if(reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Map.Entry<K, V>> task = new ReduceEntriesTask<K, V>(null, batch, 0, 0, table, null, reducer);
        
        return task.invoke();
    }
    
    
    
    /**
     * Returns the result of accumulating the given transformation
     * of all keys using the given reducer to combine values, or
     * null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case it is not combined)
     * @param reducer              a commutative associative combining function
     * @param <U>                  the return type of the transformer
     *
     * @return the result of accumulating the given transformation
     * of all keys
     *
     * @since 1.8
     */
    public <U> U reduceKeys(long parallelismThreshold, Function<? super K, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new MapReduceKeysTask<K, V, U>(null, batch, 0, 0, table, null, transformer, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all values using the given reducer to combine values, or
     * null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case it is not combined)
     * @param reducer              a commutative associative combining function
     * @param <U>                  the return type of the transformer
     *
     * @return the result of accumulating the given transformation
     * of all values
     *
     * @since 1.8
     */
    public <U> U reduceValues(long parallelismThreshold, Function<? super V, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new MapReduceValuesTask<K, V, U>(null, batch, 0, 0, table, null, transformer, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all entries using the given reducer to combine values,
     * or null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case it is not combined)
     * @param reducer              a commutative associative combining function
     * @param <U>                  the return type of the transformer
     *
     * @return the result of accumulating the given transformation
     * of all entries
     *
     * @since 1.8
     */
    public <U> U reduceEntries(long parallelismThreshold, Function<Map.Entry<K, V>, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new MapReduceEntriesTask<K, V, U>(null, batch, 0, 0, table, null, transformer, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all (key, value) pairs using the given reducer to
     * combine values, or null if none.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element, or null if there is no transformation (in
     *                             which case it is not combined)
     * @param reducer              a commutative associative combining function
     * @param <U>                  the return type of the transformer
     *
     * @return the result of accumulating the given transformation
     * of all (key, value) pairs
     *
     * @since 1.8
     */
    public <U> U reduce(long parallelismThreshold, BiFunction<? super K, ? super V, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<U> task = new MapReduceMappingsTask<K, V, U>(null, batch, 0, 0, table, null, transformer, reducer);
        
        return task.invoke();
    }
    
    
    
    /**
     * Returns the result of accumulating the given transformation
     * of all keys using the given reducer to combine values, and
     * the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all keys
     *
     * @since 1.8
     */
    public int reduceKeysToInt(long parallelismThreshold, ToIntFunction<? super K> transformer, int basis, IntBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Integer> task = new MapReduceKeysToIntTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all values using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all values
     *
     * @since 1.8
     */
    public int reduceValuesToInt(long parallelismThreshold, ToIntFunction<? super V> transformer, int basis, IntBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Integer> task = new MapReduceValuesToIntTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all entries using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all entries
     *
     * @since 1.8
     */
    public int reduceEntriesToInt(long parallelismThreshold, ToIntFunction<Map.Entry<K, V>> transformer, int basis, IntBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Integer> task = new MapReduceEntriesToIntTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all (key, value) pairs using the given reducer to
     * combine values, and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all (key, value) pairs
     *
     * @since 1.8
     */
    public int reduceToInt(long parallelismThreshold, ToIntBiFunction<? super K, ? super V> transformer, int basis, IntBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Integer> task = new MapReduceMappingsToIntTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    
    
    /**
     * Returns the result of accumulating the given transformation
     * of all keys using the given reducer to combine values, and
     * the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all keys
     *
     * @since 1.8
     */
    public long reduceKeysToLong(long parallelismThreshold, ToLongFunction<? super K> transformer, long basis, LongBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Long> task = new MapReduceKeysToLongTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all values using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all values
     *
     * @since 1.8
     */
    public long reduceValuesToLong(long parallelismThreshold, ToLongFunction<? super V> transformer, long basis, LongBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Long> task = new MapReduceValuesToLongTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all entries using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all entries
     *
     * @since 1.8
     */
    public long reduceEntriesToLong(long parallelismThreshold, ToLongFunction<Map.Entry<K, V>> transformer, long basis, LongBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Long> task = new MapReduceEntriesToLongTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all (key, value) pairs using the given reducer to
     * combine values, and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all (key, value) pairs
     *
     * @since 1.8
     */
    public long reduceToLong(long parallelismThreshold, ToLongBiFunction<? super K, ? super V> transformer, long basis, LongBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Long> task = new MapReduceMappingsToLongTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    
    
    /**
     * Returns the result of accumulating the given transformation
     * of all keys using the given reducer to combine values, and
     * the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all keys
     *
     * @since 1.8
     */
    public double reduceKeysToDouble(long parallelismThreshold, ToDoubleFunction<? super K> transformer, double basis, DoubleBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Double> task = new MapReduceKeysToDoubleTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all values using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all values
     *
     * @since 1.8
     */
    public double reduceValuesToDouble(long parallelismThreshold, ToDoubleFunction<? super V> transformer, double basis, DoubleBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Double> task = new MapReduceValuesToDoubleTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all entries using the given reducer to combine values,
     * and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all entries
     *
     * @since 1.8
     */
    public double reduceEntriesToDouble(long parallelismThreshold, ToDoubleFunction<Map.Entry<K, V>> transformer, double basis, DoubleBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Double> task = new MapReduceEntriesToDoubleTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /**
     * Returns the result of accumulating the given transformation
     * of all (key, value) pairs using the given reducer to
     * combine values, and the given basis as an identity value.
     *
     * @param parallelismThreshold the (estimated) number of elements
     *                             needed for this operation to be executed in parallel
     * @param transformer          a function returning the transformation
     *                             for an element
     * @param basis                the identity (initial default value) for the reduction
     * @param reducer              a commutative associative combining function
     *
     * @return the result of accumulating the given transformation
     * of all (key, value) pairs
     *
     * @since 1.8
     */
    public double reduceToDouble(long parallelismThreshold, ToDoubleBiFunction<? super K, ? super V> transformer, double basis, DoubleBinaryOperator reducer) {
        if(transformer == null || reducer == null) {
            throw new NullPointerException();
        }
        
        int batch = batchFor(parallelismThreshold);
        
        ForkJoinTask<Double> task = new MapReduceMappingsToDoubleTask<K, V>(null, batch, 0, 0, table, null, transformer, basis, reducer);
        
        return task.invoke();
    }
    
    /*▲ 并行操作 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /*▼ 序列化 ████████████████████████████████████████████████████████████████████████████████┓ */
    
    private static final long serialVersionUID = 7249069246763182397L;
    
    /**
     * Serialized pseudo-fields, provided only for jdk7 compatibility.
     *
     * @serialField segments Segment[]
     * The segments, each of which is a specialized hash table.
     * @serialField segmentMask int
     * Mask value for indexing into segments. The upper bits of a
     * key's hash code are used to choose the segment.
     * @serialField segmentShift int
     * Shift value for indexing within segments.
     */
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("segments", Segment[].class), new ObjectStreamField("segmentMask", Integer.TYPE), new ObjectStreamField("segmentShift", Integer.TYPE),};
    
    /**
     * Saves this map to a stream (that is, serializes it).
     *
     * @param s the stream
     *
     * @throws java.io.IOException if an I/O error occurs
     * @serialData the serialized fields, followed by the key (Object) and value
     * (Object) for each key-value mapping, followed by a null pair.
     * The key-value mappings are emitted in no particular order.
     */
    private void writeObject(ObjectOutputStream s) throws IOException {
        // For serialization compatibility
        // Emulate segment calculation from previous version of this class
        int sshift = 0;
        int ssize = 1;
        while(ssize<DEFAULT_CONCURRENCY_LEVEL) {
            ++sshift;
            ssize <<= 1;
        }
        int segmentShift = 32 - sshift;
        int segmentMask = ssize - 1;
        @SuppressWarnings("unchecked")
        Segment<K, V>[] segments = (Segment<K, V>[]) new Segment<?, ?>[DEFAULT_CONCURRENCY_LEVEL];
        for(int i = 0; i<segments.length; ++i) {
            segments[i] = new Segment<K, V>(LOAD_FACTOR);
        }
        ObjectOutputStream.PutField streamFields = s.putFields();
        streamFields.put("segments", segments);
        streamFields.put("segmentShift", segmentShift);
        streamFields.put("segmentMask", segmentMask);
        s.writeFields();
        
        Node<K, V>[] t;
        if((t = table) != null) {
            Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
            for(Node<K, V> p; (p = it.advance()) != null; ) {
                s.writeObject(p.key);
                s.writeObject(p.val);
            }
        }
        s.writeObject(null);
        s.writeObject(null);
    }
    
    /**
     * Reconstitutes this map from a stream (that is, deserializes it).
     *
     * @param s the stream
     *
     * @throws ClassNotFoundException if the class of a serialized object
     *                                could not be found
     * @throws java.io.IOException    if an I/O error occurs
     */
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        /*
         * To improve performance in typical cases, we create nodes
         * while reading, then place in table once size is known.
         * However, we must also validate uniqueness and deal with
         * overpopulated bins while doing so, which requires
         * specialized versions of putVal mechanics.
         */
        sizeCtl = -1; // force exclusion for table construction
        s.defaultReadObject();
        long size = 0L;
        Node<K, V> p = null;
        for(; ; ) {
            @SuppressWarnings("unchecked")
            K k = (K) s.readObject();
            @SuppressWarnings("unchecked")
            V v = (V) s.readObject();
            if(k != null && v != null) {
                p = new Node<K, V>(spread(k.hashCode()), k, v, p);
                ++size;
            } else {
                break;
            }
        }
        
        if(size == 0L) {
            sizeCtl = 0;
        } else {
            long ts = (long) (1.0 + size / LOAD_FACTOR);
            int n = (ts >= (long) MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : tableSizeFor((int) ts);
            @SuppressWarnings("unchecked")
            Node<K, V>[] tab = (Node<K, V>[]) new Node<?, ?>[n];
            int mask = n - 1;
            long added = 0L;
            while(p != null) {
                boolean insertAtFront;
                Node<K, V> next = p.next, first;
                int h = p.hash, j = h & mask;
                if((first = tabAt(tab, j)) == null) {
                    insertAtFront = true;
                } else {
                    K k = p.key;
                    if(first.hash<0) {
                        TreeBin<K, V> t = (TreeBin<K, V>) first;
                        if(t.putTreeVal(h, k, p.val) == null) {
                            ++added;
                        }
                        insertAtFront = false;
                    } else {
                        int binCount = 0;
                        insertAtFront = true;
                        Node<K, V> q;
                        K qk;
                        for(q = first; q != null; q = q.next) {
                            if(q.hash == h && ((qk = q.key) == k || (qk != null && k.equals(qk)))) {
                                insertAtFront = false;
                                break;
                            }
                            ++binCount;
                        }
                        if(insertAtFront && binCount >= TREEIFY_THRESHOLD) {
                            insertAtFront = false;
                            ++added;
                            p.next = first;
                            TreeNode<K, V> hd = null, tl = null;
                            for(q = p; q != null; q = q.next) {
                                TreeNode<K, V> t = new TreeNode<K, V>(q.hash, q.key, q.val, null, null);
                                if((t.prev = tl) == null) {
                                    hd = t;
                                } else {
                                    tl.next = t;
                                }
                                tl = t;
                            }
                            setTabAt(tab, j, new TreeBin<K, V>(hd));
                        }
                    }
                }
                if(insertAtFront) {
                    ++added;
                    p.next = first;
                    // 设置tab[j]为p
                    setTabAt(tab, j, p);
                }
                p = next;
            }
            table = tab;
            sizeCtl = n - (n >>> 2);
            baseCount = added;
        }
    }
    
    /*▲ 序列化 ████████████████████████████████████████████████████████████████████████████████┛ */
    
    
    
    /**
     * Returns the hash code value for this {@link Map}, i.e.,
     * the sum of, for each key-value pair in the map,
     * {@code key.hashCode() ^ value.hashCode()}.
     *
     * @return the hash code value for this map
     */
    public int hashCode() {
        int h = 0;
        Node<K, V>[] t;
        if((t = table) != null) {
            Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
            for(Node<K, V> p; (p = it.advance()) != null; )
                h += p.key.hashCode() ^ p.val.hashCode();
        }
        return h;
    }
    
    /**
     * Compares the specified object with this map for equality.
     * Returns {@code true} if the given object is a map with the same
     * mappings as this map.  This operation may return misleading
     * results if either map is concurrently modified during execution
     * of this method.
     *
     * @param o object to be compared for equality with this map
     *
     * @return {@code true} if the specified object is equal to this map
     */
    public boolean equals(Object o) {
        if(o != this) {
            if(!(o instanceof Map)) {
                return false;
            }
            
            Map<?, ?> m = (Map<?, ?>) o;
            Node<K, V>[] t;
            int f = (t = table) == null ? 0 : t.length;
            Traverser<K, V> it = new Traverser<K, V>(t, f, 0, f);
            for(Node<K, V> p; (p = it.advance()) != null; ) {
                V val = p.val;
                Object v = m.get(p.key);
                if(v == null || (v != val && !v.equals(val))) {
                    return false;
                }
            }
            
            for(Map.Entry<?, ?> e : m.entrySet()) {
                Object mk, mv, v;
                if((mk = e.getKey()) == null || (mv = e.getValue()) == null || (v = get(mk)) == null || (mv != v && !mv.equals(v))) {
                    return false;
                }
            }
        }
        return true;
    }
    
    /**
     * Returns a string representation of this map.  The string
     * representation consists of a list of key-value mappings (in no
     * particular order) enclosed in braces ("{@code {}}").  Adjacent
     * mappings are separated by the characters {@code ", "} (comma
     * and space).  Each key-value mapping is rendered as the key
     * followed by an equals sign ("{@code =}") followed by the
     * associated value.
     *
     * @return a string representation of this map
     */
    public String toString() {
        Node<K, V>[] t;
        int f = (t = table) == null ? 0 : t.length;
        Traverser<K, V> it = new Traverser<K, V>(t, f, 0, f);
        StringBuilder sb = new StringBuilder();
        sb.append('{');
        Node<K, V> p;
        if((p = it.advance()) != null) {
            for(; ; ) {
                K k = p.key;
                V v = p.val;
                sb.append(k == this ? "(this Map)" : k);
                sb.append('=');
                sb.append(v == this ? "(this Map)" : v);
                if((p = it.advance()) == null)
                    break;
                sb.append(',').append(' ');
            }
        }
        return sb.append('}').toString();
    }
    
    
    
    /* ---------------- Static utilities -------------- */
    
    /**
     * Spreads (XORs) higher bits of hash to lower and also forces top
     * bit to 0. Because the table uses power-of-two masking, sets of
     * hashes that vary only in bits above the current mask will
     * always collide. (Among known examples are sets of Float keys
     * holding consecutive whole numbers in small tables.)  So we
     * apply a transform that spreads the impact of higher bits
     * downward. There is a tradeoff between speed, utility, and
     * quality of bit-spreading. Because many common sets of hashes
     * are already reasonably distributed (so don't benefit from
     * spreading), and because we use trees to handle large sets of
     * collisions in bins, we just XOR some shifted bits in the
     * cheapest possible way to reduce systematic lossage, as well as
     * to incorporate impact of the highest bits that would otherwise
     * never be used in index calculations because of table bounds.
     */
    /**
     * 计算Node节点hash值的算法：参数h为hash值
     * eg:
     * h二进制为 --> 	 		 		    1100 0011 1010 0101 0001 1100 0001 1110
     * (h >>> 16) -->  					0000 0000 0000 0000 1100 0011 1010 0101
     * (h ^ (h >>> 16)) -->				1100 0011 1010 0101 1101 1111 1011 1011
     * 注：(h ^ (h >>> 16)) 目的是让h的高16位也参与寻址计算，使得到的hash值更分散，减少hash冲突产生~
     * ------------------------------------------------------------------------------
     * HASH_BITS -->					0111 1111 1111 1111 1111 1111 1111 1111
     * (h ^ (h >>> 16)) -->				1100 0011 1010 0101 1101 1111 1011 1011
     * (h ^ (h >>> 16)) & HASH_BITS --> 0100 0011 1010 0101 1101 1111 1011 1011
     * 注： (h ^ (h >>> 16))得到的结果再& HASH_BITS，目的是为了让得到的hash值结果始终是一个正数
     */
    static final int spread(int h) {
        return (h ^ (h >>> 16)) & HASH_BITS;
    }
    
    /**
     * Returns a power of two table size for the given desired capacity.
     * See Hackers Delight, sec 3.2
     */
    /*
     * 根据预期的容量cap计算出ConcurrentHashMap中的哈希数组实际需要分配的容量
     * 如果输入值是2的冪，则原样返回，如果不是2的冪，则向上取就近的冪
     * 比如输入13，返回16，输入17，返回32
     */
    /**
     * 根据c,计算得到大于等于c的，最小2的次幂数，该方法在HashMap源码中分析过~
     * eg：c = 28 ，则计算得到的返回结果为 32
     * c = 28 ==> n=27 => 0b 11011
     *
     * 11011 | 01101 => 11111 ---- n |= n >>> 1
     * 11111 | 00111 => 11111 ---- n |= n >>> 2
     * ....
     * => 11111 + 1 = 100000 = 32
     */
    private static final int tableSizeFor(int cap) {
        int n = -1 >>> Integer.numberOfLeadingZeros(cap - 1);
        return (n<0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }
    
    /**
     * Returns x's Class if it is of the form "class C implements
     * Comparable<C>", else null.
     */
    // 用于红黑树元素比较
    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c; Type[] ts, as; ParameterizedType p;
            
            // bypass checks
            if ((c = x.getClass()) == String.class) {
                return c;
            }
            
            if ((ts = c.getGenericInterfaces()) != null) {
                for (Type t : ts) {
                    if ((t instanceof ParameterizedType)
                        && ((p = (ParameterizedType)t).getRawType() == Comparable.class)
                        && (as = p.getActualTypeArguments()) != null
                        && as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        
        return null;
    }
    
    /**
     * Returns k.compareTo(x) if x matches kc (k's screened comparable
     * class), else 0.
     */
    // 用于红黑树元素比较
    @SuppressWarnings({"rawtypes","unchecked"}) // for cast to Comparable
    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 : ((Comparable)k).compareTo(x));
    }
    
    
    /* ---------------- Table element access -------------- */
    
    /*
     * Atomic access methods are used for table elements as well as
     * elements of in-progress next table while resizing.  All uses of
     * the tab arguments must be null checked by callers.  All callers
     * also paranoically precheck that tab's length is not zero (or an
     * equivalent check), thus ensuring that any index argument taking
     * the form of a hash value anded with (length - 1) is a valid
     * index.  Note that, to be correct wrt arbitrary concurrency
     * errors by users, these checks must operate on local variables,
     * which accounts for some odd-looking inline assignments below.
     * Note that calls to setTabAt always occur within locked regions,
     * and so require only release ordering.
     */

    /**
     * 获取 tab(Node[]) 数组指定下标 i 的Node节点
     * Node<K,V>[] tab：表示Node[]数组
     * int i：表示数组下标
     */
    @SuppressWarnings("unchecked")
    static final <K, V> Node<K, V> tabAt(Node<K, V>[] tab, int i) {
        // 计算下标i的元素在底层的偏移地址
        long offset = ((long) i << ASHIFT) + ABASE;
        
        // 获取对象tab中offset地址处对应的引用类型字段的值
        return (Node<K, V>) U.getObjectAcquire(tab, offset);
    }

    /**
     * 通过CAS的方式去向Node数组指定位置i设置节点值，设置成功返回true，否则返回false
     * Node<K,V>[] tab：表示Node[]数组
     * int i：表示数组下标
     * Node<K,V> c：期望节点值
     * Node<K,V> v：要设置的节点值
     */
    static final <K, V> boolean casTabAt(Node<K, V>[] tab, int i, Node<K, V> expected, Node<K, V> node) {
        // 计算下标i的元素在底层的偏移地址
        long offset = ((long) i << ASHIFT) + ABASE;
        // 调用Unsafe的比较并交换去设置Node[]数组指定位置的节点值，参数如下：
        // tab：Node[]数组
        // ((long)i << ASHIFT) + ABASE：下标为i数组桶的偏移地址
        // c：期望节点值
        // v：要设置的节点值
        return U.compareAndSetObject(tab, offset, expected, node);
    }

    /**
     * 根据数组下标i，设置Node[]数组指定下标位置的节点值：
     * Node<K,V>[] tab：表示Node[]数组
     * int i：表示数组下标
     * Node<K,V> v：要设置的节点值
     */
    static final <K, V> void setTabAt(Node<K, V>[] tab, int i, Node<K, V> x) {
        // 计算下标i的元素在底层的偏移地址
        long offset = ((long) i << ASHIFT) + ABASE;
        // ((long)i << ASHIFT) + ABASE：下标为i数组桶的偏移地址
        U.putObjectRelease(tab, offset, x);
    }
    
    
    // Original (since JDK1.2) Map methods
    
    /*
     * 向当前Map中存入新的元素，并返回旧元素
     *
     * onlyIfAbsent 是否需要维持原状（不覆盖旧值）
     */
    // 向并发Map中put一个数据
    // Key: 数据的键
    // value：数据的值
    // onlyIfAbsent：是否替换数据：
    // 如果为false，则当put数据时，遇到Map中有相同K,V的数据，则将其替换
    // 如果为true，则当put数据时，遇到Map中有相同K,V的数据，则不做替换，不插入
    final V putVal(K key, V value, boolean onlyIfAbsent) {
        // 控制 k 和 v 不能为null
        if (key == null || value == null) {
            throw new NullPointerException();
        }
        
        /*
         * 计算key的哈希值，在这个过程中会调用key的hashCode()方法
         * 通过spread方法，可以让高位也能参与进寻址运算，使最终得到的hash值更分散
         * key是一个对象的引用（可以看成地址）
         * 理论上讲，key的值是否相等，跟计算出的哈希值是否相等，没有必然联系，一切都取决于hashCode()这个方法
         */
        int hash = spread(key.hashCode());
        // binCount表示当前k-v 封装成node插入到指定桶位后，在桶位中的所属链表的下标位置
        // =0 表示当前桶位为null，node可以直接放入
        // >0 表示当前桶位中有节点，遍历链表，将封装k-v的新node放入链表末尾，并记录链表末尾的下标binCount
        // =2 表示当前桶位**可能**已经树化为红黑树了
        int binCount = 0;
        
        Node<K, V>[] tab = table;
        
        while (true) {
            Node<K, V> f;   // 指向待插入元素应当插入的位置
            int fh;         // 元素f对应的哈希值
            K fk;           // 元素f中的key
            V fv;           // 元素f中的value
            
            int len;        // 哈希数组容量
            int i;          // 当前key在哈希数组上的索引

            // CASE1：成立，表示当前map中的table尚未初始化...
            if (tab == null || (len = tab.length) == 0) {
                // 初始化哈希数组
                tab = initTable();
            }

            // CASE2：table已经初始化，此时根据寻址算法确定一个桶，并且桶的头结点f为null
            // i 表示key使用路由寻址算法得到key对应table数组的下标位置，tabAt方法获取指定桶位i的头结点f
            else if((f = tabAt(tab, i = (len - 1) & hash)) == null) {
                // node是相应哈希槽处的首个元素
                Node<K, V> node = new Node<>(hash, key, value);
                
                // 原子地更新tab[i]为node
                if (casTabAt(tab, i, null, node)) {
                    // 跳出外循环
                    break;                   // no lock when adding to empty bin
                }
            }

            // -----------------------------------------------------------------------------
            // CASE3：table已经初始化，寻址得到的桶位中的头结点f不是null，如果该头结点f的hash值fh=-1：
            // 则，表示当前节点是FWD(forwarding)节点
            // 如果CASE3条件成立：表示当前桶位的头结点为 FWD结点，表示目前map正处于扩容过程中..
            else if ((fh = f.hash) == MOVED) {
                tab = helpTransfer(tab, f);
            }

            // -----------------------------------------------------------------------------
            // 如果待插入元素所在的哈希槽上已经有别的结点存在，且当前状态不是在扩容当中，那么首先判断该结点是否为同位元素
            // 如果遇到了同位元素，但不允许覆盖存储，则直接返回待插入的值
            else if (onlyIfAbsent // 如果不允许覆盖存储
                && fh == hash && ((fk = f.key) == key || (fk != null && key.equals(fk))) && (fv = f.val) != null) { // 如果遇到了同位元素
                return fv;
            }

            // -----------------------------------------------------------------------------
            // CASE4：CASE1-3都不满足时，那么当前桶位存放的可能是链表也可能是红黑树代理结点TreeBin
            else {
                // 保留替换之前的数据引用：当新插入的key存在后，会将旧值赋给OldVal，返回给put方法调用
                V oldVal = null;

                // 使用synchronized加锁“头节点”（**理论上是“头结点”**)
                synchronized(f) {
                    // -----------------------------------------------------------------------
                    // CASE5：tabAt(tab, i) == f
                    // 对比一下当前桶位的头节点是否为之前获取的头结点：为什么又要对比一下？
                    // 如果其它线程在当前线程之前将该桶位的头结点修改掉了，当前线程再使用sync对该节点f加锁就有问题了（锁本身加错了地方~）
                    if (tabAt(tab, i) == f) { // 如果条件成立，说明加锁的对象f没有问题，持有锁！
                        // ------------------------------------------------------------------
                        // CASE6：fh >= 0)
                        // 如果条件成立，说明当前桶位就是普通链表桶位,这里回顾下常量属性字段：
                        // static final int MOVED = -1; 表示当前节点是FWD(forwarding)节点
                        // static final int TREEBIN = -2; 表示当前节点已经树化
                        // static final int RESERVED = -3; 表示当前节点为占位节点
                        if (fh >= 0) {
                            // 1.当前插入key与链表当中所有元素的key都不一致时，当前的插入操作是追加到链表的末尾，binCount此时表示链表长度
                            // 2.当前插入key与链表当中的某个元素的key一致时，当前插入操作可能就是替换了。binCount表示冲突位置（binCount - 1）
                            binCount = 1;

                            // 迭代循环当前桶位的链表，e是每次循环处理节点。
                            for (Node<K, V> e = f; ; ++binCount) {
                                // 当前循环遍历节点的key
                                K ek;
                                
                                // 找到了同位元素，替换旧元素或者跳出循环
                                // --------------------------------------------------------
                                // CASE7：
                                // 条件一：e.hash == hash
                                // 成立：表示循环的当前元素的hash值与插入节点的hash值一致,需要进一步判断
                                // 条件二：((ek = e.key) == key ||(ek != null && key.equals(ek)))
                                // 成立：说明循环的当前节点与插入节点的key一致，确实发生冲突了~
                                if (e.hash == hash
                                        && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    // 将当前循环的元素的值赋值给oldVal
                                    oldVal = e.val;

                                    // 传入的putVal方法参数onlyIfAbsent：是否替换数据：
                                    // false，当put数据时，遇到Map中有相同K,V的数据，则将其替换
                                    // true，当put数据时，遇到Map中有相同K,V的数据，则不做替换，不插入
                                    if(!onlyIfAbsent) {
                                        e.val = value;
                                    }
                                    // 跳出内循环
                                    break;
                                }

                                // --------------------------------------------------------
                                // CASE8：
                                // 当前元素与插入元素的key不一致时，会走下面程序:
                                // 1.更新循环遍历的节点为当前节点的下一个节点
                                // 2.判断下一个节点是否为null，如果是null，说明当前节点已经是队尾了，插入数据需要追加到队尾节点的后面。
                                Node<K, V> pred = e;
                                e = e.next;
                                // 无法找到同位元素的话，说明需要在哈希槽(链)末尾新增元素
                                if (e == null) {
                                    pred.next = new Node<K, V>(hash, key, value);
                                    // 跳出内循环
                                    break;
                                }
                            } // for
                        }

                        // ------------------------------------------------------------------
                        // CASE9：f instanceof TreeBin
                        // 如果条件成立，表示当前桶位是红黑树代理结点TreeBin
                        //（前置条件：该桶位一定不是链表）
                        else if (f instanceof TreeBin) {
                            // p表示红黑树中如果与你插入节点的key 有冲突节点的话，则putTreeVal方法会返回冲突节点的引用。
                            Node<K, V> p;
                            // 强制设置binCount为2，因为binCount <= 1 时有其它含义，所以这里设置为了2 （回头讲addCount的时候会详细介绍）
                            binCount = 2;
                            // 条件一成立，说明当前插入节点的key与红黑树中的某个节点的key一致，冲突了：
                            // putTreeVal向红黑树中插入结点，插入成功返回null，否则返回冲突结点对象
                            if ((p = ((TreeBin<K, V>) f).putTreeVal(hash, key, value)) != null) {
                                // 将冲突节点的值赋值给oldVal
                                oldVal = p.val;
                                if (!onlyIfAbsent) {
                                    p.val = value;
                                }
                            }
                        }
                        // 解决 computeIfAbsent bug
                        // @see http://gee.cs.oswego.edu/cgi-bin/viewcvs.cgi/jsr166/src/main/java/util/concurrent/ConcurrentHashMap.java?r1=1.258&r2=1.259&sortby=date&diff_format=f
                        else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                } // synchronized

                // ------------------------------------------------------------------
                // CASE10：binCount != 0
                // 说明当前桶位不为null，可能是红黑树也可能是链表
                if (binCount != 0) {
                    // 如果binCount>=8 表示处理的桶位一定是链表
                    // 哈希槽（链）上的元素数量增加到 TREEIFY_THRESHOLD后，这些元素进入波动期，即将从链表转换为红黑树
                    if (binCount >= TREEIFY_THRESHOLD) {
                        // 因为桶中链表长度大于了8，需要树化：
                        // 调用转化链表为红黑树的方法
                        treeifyBin(tab, i);
                    }
                    // 说明当前线程插入的数据key，与原有k-v发生冲突，需要将原数据v返回给调用者。
                    if (oldVal != null) {
                        return oldVal;
                    }
                    
                    break;
                }
            }
        } // while

        // Map中的元素数据量累加方法：有额外的以下功能
        // 1.统计当前table一共有多少数据
        // 2.并判断是否达到扩容阈值标准，触发扩容。
        addCount(1L, binCount);
        return null;
    }
    
    /**
     * Implementation for the four public remove/replace methods:
     * Replaces node value with v, conditional upon match of cv if non-null.
     * If resulting value is null, delete.
     */
    /*
     * 根据key查找同位元素，如果找不到，直接返回null
     * 如果存在同位元素，则：
     * 　　如果cv不为空，且不等于旧值，仍然返回null
     * 　　如果cv为null，或者cv等于旧值，则：
     * 　　　　如果newValue不为空，用新值覆盖旧值
     * 　　　　如果newValue为null，移除旧值
     */
    /**
     * 结点替换：
     * 参数1：Object key -> 就表示当前结点的key
     * 参数2：V value -> 要替换的目标值
     * 参数3：Object cv（compare Value） ->
     * 			如果cv不为null，则需要既比对key，还要比对cv，这样个参数都一致，才能替换成目标值
     */
    final V replaceNode(Object key, V newValue, Object cv) {
        // 计算key经过扰动运算后得到的hash
        int hash = spread(key.hashCode());
        
        Node<K,V>[] tab = table;
        // 自旋
        for(; ; ) {
            // f表示桶位头结点
            // n表示当前table数组长度
            // i表示hash命中桶位下标
            // fh表示桶位头结点hash
            Node<K,V> f; int n, i, fh;

            // ----------------------------------------------------------------------------
            // CASE1：
            // 条件一：tab == null
            //					true -> 表示当前map.table尚未初始化..
            //					false -> 表示当前map.table已经初始化
            // 条件二：(n = tab.length) == 0
            //					true -> 表示当前map.table尚未初始化..
            //					false -> 已经初始化
            // 条件三：(f = tabAt(tab, i = (n - 1) & hash)) == null
            //					true -> 表示命中桶位中为null，直接break
            if (tab == null
                    || (n = tab.length) == 0
                    || (f = tabAt(tab, i = (n - 1) & hash)) == null) {
                // 如果目标key所在的桶不存在，跳出循环返回null
                break;
            }
            // ----------------------------------------------------------------------------
            // CASE2：
            // 前置条件CASE2 ~ CASE3：当前桶位不是null
            // 条件成立：fwd结点，说明当前table正在扩容中，当前是个写操作，所以当前线程需要协助table完成扩容。
            else if ((fh = f.hash) == MOVED) {
                // 如果正在扩容中，则协助扩容
                tab = helpTransfer(tab, f);
            }
            // ----------------------------------------------------------------------------
            // CASE3:
            // 前置条件CASE2 ~ CASE3：当前桶位不是null
            // 当前桶位是一个有数据的桶位，桶中可能是 "链表"也可能是"红黑树"TreeBin
            else {
                // 保留替换之前的数据引用
                V oldVal = null;
                
                // 是否处理过结点
                // 校验标记,在下面的CASEn中的if判断使用：标记是否处理过
                boolean validated = false;
                // 加锁当前桶位头结点，加锁成功之后会进入代码块。
                synchronized (f) {
                    // 判断sync加锁是否为当前桶位头节点，防止其它线程，在当前线程加锁成功之前，修改过桶位 的头结点，导致锁错对象！

                    // --------------------------------------------------------------------
                    // CASE4:  tabAt(tab, i) == f 再次验证当前桶第一个元素是否被修改过
                    // 条件成立：说明当前桶位头结点仍然为f，其它线程没修改过！
                    if (tabAt(tab, i) == f) {
                        // --------------------------------------------------------------------
                        // CASE5:  fh >= 0
                        // 条件成立：说明桶位为链表或者单个node
                        if (fh >= 0) {
                            // 校验标记置为true
                            validated = true;

                            // e 表示当前循环处理结点
                            // pred 表示当前循环节点的上一个节点
                            Node<K,V> e = f;
                            Node<K,V> pred = null;
                            // 遍历链表寻找目标节点
                            while(true) {
                                // 表示当前节点key
                                K ek;

                                // ------------------------------------------------------------
                                // CASE6:
                                // 条件一：e.hash == hash
                                //			true->说明当前节点的hash与查找节点hash一致
                                // 条件二：((ek = e.key) == key || (ek != null && key.equals(ek)))
                                // CASE6的if条件成立，说明key 与查询的key完全一致。
                                if (e.hash == hash && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    // 找到了目标节点：当前节点的value，
                                    V ev = e.val;
                                    // -----------------------------------------------------
                                    // CASE7:  检查目标节点旧value是否等于cv
                                    // 条件一：cv == null
                                    //			true -> 替换的值为null那么就是一个删除操作
                                    // 条件二：cv == ev || (ev != null && cv.equals(ev))
                                    //			true -> 那么是一个替换操作
                                    if (cv == null || cv == ev || (ev != null && cv.equals(ev))) {
                                        // 删除 或者 替换
                                        // 将当前节点的值 赋值给 oldVal 后续返回会用到~
                                        oldVal = ev;
                                        // 目标value不等于null
                                        // 如果条件成立：说明当前是一个替换操作
                                        if (newValue != null) {
                                            // 覆盖旧值
                                            e.val = newValue;
                                        }
                                        // 删除操作
                                        else {
                                            // 如果前置节点不为空，删除当前节点：
                                            // 让当前节点的上一个节点，指向当前节点的下一个节点。
                                            if (pred == null) {
                                                // 设置tab[i]为e.next
                                                setTabAt(tab, i, e.next);
                                            }
                                            // 条件成里：说明当前节点即为头结点
                                            else {
                                                // 如果前置节点为空，说明是桶中第一个元素，删除之：
                                                // 只需要将桶位设置为头结点的下一个节点。
                                                pred.next = e.next;
                                            }
                                        }
                                    }
                                    break;
                                }
                                
                                pred = e;
                                // 遍历到链表尾部还没找到元素，跳出循环
                                if ((e = e.next) == null) {
                                    break;
                                }
                            }// while(true)
                        }
                        // --------------------------------------------------------------------
                        // CASE8:  f instanceof TreeBin
                        // 条件成立：TreeBin节点。
                        else if (f instanceof TreeBin) {
                            // 校验标记置为true
                            validated = true;
                            // 转换为实际类型 TreeBin t
                            TreeBin<K,V> t = (TreeBin<K,V>)f;
                            // r 表示 红黑树根节点
                            // p 表示 红黑树中查找到对应key 一致的node
                            TreeNode<K,V> r, p;

                            // 遍历树找到了目标节点：
                            // 条件一：(r = t.root) != null 理论上是成立
                            // 条件二：TreeNode.findTreeNode 以当前节点为入口，向下查找key（包括本身节点）
                            //        true->说明查找到相应key 对应的node节点，会赋值给p
                            if ((r = t.root) != null &&
                                (p = r.findTreeNode(hash, key, null)) != null) {
                                // 保存p.val 到pv
                                V pv = p.val;
                                // 检查目标节点旧value是否等于cv：
                                // 条件一：cv == null 成立：不必对比value，就做替换或者删除操作
                                // 条件二：cv == pv ||(pv != null && cv.equals(pv)) 成立：说明“对比值”与当前p节点的值 一致
                                if (cv == null
                                        || cv == pv
                                        || (pv != null && cv.equals(pv))) {
                                    // 替换或者删除操作
                                    oldVal = pv;
                                    // 如果value不为空则替换旧值
                                    // 条件成立：替换操作
                                    if (newValue != null) {
                                        p.val = newValue;
                                    }
                                    // 如果value为空则删除元素
                                    // 删除操作
                                    else if (t.removeTreeNode(p)) {
                                        Node<K, V> x = untreeify(t.first);
                                        // 如果删除后树的元素个数较少则退化成链表
                                        // t.removeTreeNode(p)这个方法返回true表示删除节点后树的元素个数较少
                                        setTabAt(tab, i, x);
                                    }
                                }
                            }
                        }
                        // --------------------------------------------------------------------
                        // CASE9:  f instanceof ReservationNode
                        // 条件成立：说明桶位为占位节点
                        else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }

                    }
                }// synchronized
                
                // 如果处理过结点，则需要进一步验证
                // ----------------------------------------------------------------------------
                // CASEn: 如果处理过，不管有没有找到元素都返回
                // 当其他线程修改过桶位头结点时，当前线程 sync 头结点 锁错对象时，validated 为false，会进入下次for自旋:
                if (validated) {
                    // 如果找到了元素，返回其旧值
                    if (oldVal != null) {
                        // 替换的值 为null，说明当前是一次删除操作，oldVal ！=null 成立，说明删除成功，更新当前元素个数计数器。
                        // 如果要替换的值为空，元素个数减1
                        if (newValue == null) {
                            addCount(-1L, -1);
                        }
                        return oldVal;
                    }
                    break;
                }
            }
        } // for(; ; )
        // 没找到元素返回空
        return null;
    }
    
    
    // Overrides of JDK8+ Map extension method defaults
    
    /**
     * Helper method for EntrySetView.removeIf.
     */
    boolean removeEntryIf(Predicate<? super Entry<K,V>> function) {
        if (function == null) throw new NullPointerException();
        Node<K,V>[] t;
        boolean removed = false;
        if ((t = table) != null) {
            Traverser<K,V> it = new Traverser<K,V>(t, t.length, 0, t.length);
            for (Node<K,V> p; (p = it.advance()) != null; ) {
                K k = p.key;
                V v = p.val;
                Map.Entry<K,V> e = new AbstractMap.SimpleImmutableEntry<>(k, v);
                if (function.test(e) && replaceNode(k, null, v) != null) {
                    removed = true;
                }
            }
        }
        return removed;
    }
    
    /**
     * Helper method for ValuesView.removeIf.
     */
    boolean removeValueIf(Predicate<? super V> function) {
        if (function == null) throw new NullPointerException();
        Node<K,V>[] t;
        boolean removed = false;
        if ((t = table) != null) {
            Traverser<K,V> it = new Traverser<K,V>(t, t.length, 0, t.length);
            for (Node<K,V> p; (p = it.advance()) != null; ) {
                K k = p.key;
                V v = p.val;
                if (function.test(v) && replaceNode(k, null, v) != null) {
                    removed = true;
                }
            }
        }
        return removed;
    }
    
    
    // ConcurrentHashMap-only methods
    
    /**
     * Returns the number of mappings. This method should be used
     * instead of {@link #size} because a ConcurrentHashMap may
     * contain more mappings than can be represented as an int. The
     * value returned is an estimate; the actual count may differ if
     * there are concurrent insertions or removals.
     *
     * @return the number of mappings
     * @since 1.8
     */
    public long mappingCount() {
        long n = sumCount();
        return (n < 0L) ? 0L : n; // ignore transient negative values
    }
    
    /**
     * Creates a new {@link Set} backed by a ConcurrentHashMap
     * from the given type to {@code Boolean.TRUE}.
     *
     * @param <K> the element type of the returned set
     * @return the new set
     * @since 1.8
     */
    public static <K> KeySetView<K,Boolean> newKeySet() {
        return new KeySetView<K,Boolean>(new ConcurrentHashMap<K,Boolean>(), Boolean.TRUE);
    }
    
    /**
     * Creates a new {@link Set} backed by a ConcurrentHashMap
     * from the given type to {@code Boolean.TRUE}.
     *
     * @param initialCapacity The implementation performs internal
     * sizing to accommodate this many elements.
     * @param <K> the element type of the returned set
     * @return the new set
     * @throws IllegalArgumentException if the initial capacity of
     * elements is negative
     * @since 1.8
     */
    public static <K> KeySetView<K,Boolean> newKeySet(int initialCapacity) {
        return new KeySetView<K,Boolean>(new ConcurrentHashMap<K,Boolean>(initialCapacity), Boolean.TRUE);
    }
    
    /**
     * Returns a {@link Set} view of the keys in this map, using the
     * given common mapped value for any additions (i.e., {@link
     * Collection#add} and {@link Collection#addAll(Collection)}).
     * This is of course only appropriate if it is acceptable to use
     * the same value for all additions from this view.
     *
     * @param mappedValue the mapped value to use for any additions
     * @return the set view
     * @throws NullPointerException if the mappedValue is null
     */
    public KeySetView<K,V> keySet(V mappedValue) {
        if (mappedValue == null) {
            throw new NullPointerException();
        }
        
        return new KeySetView<K,V>(this, mappedValue);
    }
    
    
    /* ---------------- Table Initialization and Resizing -------------- */
    
    /**
     * Returns the stamp bits for resizing a table of size n.
     * Must be negative when shifted left by RESIZE_STAMP_SHIFT.
     */
    /**
     * table数组扩容时，计算出一个扩容标识戳，当需要并发扩容时，当前线程必须拿到扩容标识戳才能参与扩容：
     */
    static final int resizeStamp(int n) {
        /**
         * 举例子分析一下：
         * 当我们需要table容量从16 库容到32时：Integer.numberOfLeadingZeros(16) 会得到 27，怎么得来的呢？
         * numberOfLeadingZeros(n) 根据传入的n，返回当前数值转换为二进制后，从高位到地位开始统计，统计有多少个0连续在一块：
         * eg：16 转换二进制 => 1 0000 则 numberOfLeadingZeros(16)的结果就是 27，因为Integer是32位，1 0000占5位，那么前面就有(32 - 5)个0，即连续最长的0的个数为27个。
         * (1 << (RESIZE_STAMP_BITS - 1))：其中RESIZE_STAMP_BITS是一个固定值16
         *
         * 下面就来计算一下：
         * // 从16扩容到32
         * 16 -> 32
         * // 用A表示：
         * numberOfLeadingZeros(16) => 1 0000 => 27 => 0000 0000 0001 1011
         * // 用B表示：
         * (1 << (RESIZE_STAMP_BITS - 1)) => (1 << (16 - 1) => 1000 0000 0000 0000 => 32768
         *
         * // A | B
         * Integer.numberOfLeadingZeros(n) | (1 << (RESIZE_STAMP_BITS - 1))
         * -----------------------------------------------------------------
         * 0000 0000 0001 1011  ---> A
         * 1000 0000 0000 0000  ---> B
         * -------------------  ---> | 按位或
         * 1000 0000 0001 1011  ---> 计算得到扩容标识戳
         */
        return Integer.numberOfLeadingZeros(n) | (1 << (RESIZE_STAMP_BITS - 1));
    }
    
    /**
     * Helps transfer if a resize is in progress.
     */
    // 协助扩容（迁移元素），当线程添加元素时发现table正在扩容，且当前元素所在的桶元素已经迁移完成了，则协助迁移其它桶的元素。当前桶元素迁移完成了才去协助迁移其它桶元素
    final Node<K, V>[] helpTransfer(Node<K, V>[] tab, Node<K, V> f) {
        // nextTab 引用的是 fwd.nextTable == map.nextTable 理论上是这样。
        // sc 保存map.sizeCtl
        Node<K, V>[] nextTab;
        int sc;

        // CASE0: 如果桶数组不为空，并且当前桶第一个元素为ForwardingNode类型，并且nextTab不为空
        // 说明当前桶已经迁移完毕了，才去帮忙迁移其它桶的元素
        // 扩容时会把旧桶的第一个元素置为ForwardingNode，并让其nextTab指向新桶数组
        // 条件一：tab != null 恒成立 true
        // 条件二：(f instanceof ForwardingNode) 恒成立 true
        // 条件三：((ForwardingNode<K,V>)f).nextTable) != null 恒成立 true
        if (tab != null && (f instanceof ForwardingNode) && (nextTab = ((ForwardingNode<K, V>) f).nextTable) != null) {

            // 根据前表的长度 tab.length 去获取扩容唯一标识戳，
            // 假设 16 -> 32 扩容：1000 0000 0001 1011
            int rs = resizeStamp(tab.length);
            // int rs = resizeStamp(tab.length) << RESIZE_STAMP_SHIFT;

            // 条件一：nextTab == nextTable
            // 成立：表示当前扩容正在进行中
            // 不成立：1.nextTable被设置为Null了，扩容完毕后，会被设为Null
            //        2.再次出发扩容了...咱们拿到的nextTab 也已经过期了...
            // 条件二：table == tab
            // 成立：说明 扩容正在进行中，还未完成
            // 不成立：说明扩容已经结束了，扩容结束之后，最后退出的线程 会设置 nextTable 为 table

            // 条件三：(sc = sizeCtl) < 0
            // 成立：说明扩容正在进行中
            // 不成立：说明sizeCtl当前是一个大于0的数，此时代表下次扩容的阈值，当前扩容已经结束。
            while (nextTab == nextTable && table == tab && (sc = sizeCtl) < 0) {

                // 条件一：(sc >>> RESIZE_STAMP_SHIFT) != rs
                //        true -> 说明当前线程获取到的扩容唯一标识戳 非 本批次扩容
                //        false -> 说明当前线程获取到的扩容唯一标识戳 是 本批次扩容
                // 条件二：JDK1.8 中有bug jira已经提出来了 其实想表达的是 =  sc == (rs << 16 ) + 1
                //        true -> 表示扩容完毕，当前线程不需要再参与进来了
                //        false -> 扩容还在进行中，当前线程可以参与
                // 条件三：JDK1.8 中有bug jira已经提出来了 其实想表达的是 = sc == (rs<<16) + MAX_RESIZERS
                //        true -> 表示当前参与并发扩容的线程达到了最大值 65535 - 1
                //        false -> 表示当前线程可以参与进来
                // 条件四：transferIndex <= 0
                //        true -> 说明map对象全局范围内的任务已经分配完了，当前线程进去也没活干..
                //        false -> 还有任务可以分配。
                if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 || sc == rs + MAX_RESIZERS || transferIndex <= 0) {
                    break;
                }
                // 扩容线程数加1
                if (U.compareAndSetInt(this, SIZECTL, sc, sc + 1)) {
                    // 当前线程帮忙迁移元素
                    transfer(tab, nextTab);
                    break;
                }
            }
            
            return nextTab;
        }
        
        return table;
    }
    
    /**
     * Initializes table, using the size recorded in sizeCtl.
     */
    // 初始化哈希数组
    private final Node<K, V>[] initTable() {
        // tab: 引用map.table
        // sc: sizeCtl的临时值
        // sizeCtl：默认为0，用来控制table的状态、以及初始化和扩容操作:
        // sizeCtl<0表示table的状态:
        //（1）=-1，表示有其他线程正在进行初始化操作。（其他线程就不能再进行初始化，相当于一把锁）
        //（2）=-(1 + nThreads)，表示有n个线程正在一起扩容。
        // sizeCtl>=0表示table的初始化和扩容相关操作：
        //（3）=0，默认值，后续在真正初始化table的时候使用，设置为默认容量DEFAULT_CAPACITY --> 16。
        //（4）>0，将sizeCtl设置为table初始容量或扩容完成后的下一次扩容的门槛。
        Node<K, V>[] tab;

        // 附加条件的自旋： 条件是map.table尚未初始化...
        while ((tab = table) == null || tab.length == 0) {
            
            // -----------------------------------------------------------------------------
            // CASE1: sizeCtl) < 0
            // sizeCtl < 0可能是以下2种情况：
            //（1）-1，表示有其他线程正在进行table初始化操作。
            //（2）-(1 + nThreads)，表示有n个线程正在一起扩容。
            int sc = sizeCtl;
            if (sc < 0) {
                // 这里sizeCtl大概率就是-1，表示其它线程正在进行创建table的过程，当前线程没有竞争到初始化table的锁，进而当前线程被迫等待...
                Thread.yield(); // lost initialization race; just spin
            }

            // -----------------------------------------------------------------------------
            // CASE2：sizeCtl) >= 0 且U.compareAndSwapInt(this, SIZECTL, sc, -1)结果为true
            // U.compareAndSwapInt(this, SIZECTL, sc, -1)：以CAS的方式修改当前线程的sizeCtl为-1，
            // sizeCtl如果成功被修改为-1，就返回true，否则返回false。
            // 当返回true时，则该线程就可以进入下面的else if代码块中，这时候sizeCtl=-1相当于是一把锁，表示下面的else if代码块已经被该线程占用，其他线程不能再进入~
            else if(U.compareAndSetInt(this, SIZECTL, sc, -1)) {
                try {
                    // ----------------------------------------------------------------------
                    // CASE3: 这里为什么又要判断呢？
                    // 为了防止其它线程已经初始化table完毕了，然后当前线程再次对其初始化..导致丢失数据。
                    // 如果条件成立，说明其它线程都没有进入过这个if块，当前线程就是具备初始化table权利了。
                    if ((tab = table) == null || tab.length == 0) {
                        // sc大于等于0的情况如下：
                        //（3）=0，默认值，后续在真正初始化table的时候使用，设置为默认容量DEFAULT_CAPACITY --> 16。
                        //（4）>0，将sizeCtl设置为table初始容量或扩容完成后的下一次扩容的门槛。
                        // 如果sc大于0,则创建table时使用sc为指定table初始容量大小，
                        // 否则使用16默认值DEFAULT_CAPACITY
                        int len = (sc>0) ? sc : DEFAULT_CAPACITY;
                        
                        // 创建新的哈希数组
                        @SuppressWarnings("unchecked")
                        Node<K, V>[] newTable = (Node<K, V>[]) new Node<?, ?>[len];
                        // 将新数组nt赋值给table、tab
                        table = tab = newTable;
                        // sc设置为下次散列表扩容的门槛：0.75n
                        sc = len - (len >>> 2);
                    }
                } finally {
                    // 将sc赋值给sizeCtl，分为一下2种情况：
                    // 1、当前线程既通过了CASE2的判断，也通过了CASE3的判断：
                    // 则，当前线程是第一次创建map.table的线程，那么，sc就表示下一次扩容的阈值。
                    // 2、当线程通过了CASE2的判断，但是没有通过CASE3的判断：
                    // 则，当前线程并不是第一次创建map.table的线程，当前线程通过CASE2的判断时，将
                    // sizeCtl设置为了-1 ，那么在该线程结束上面的代码逻辑之后，需要将sc修改回进入CASE2之前的sc值。
                    sizeCtl = sc;
                }
                
                break;
            }
        }
        
        return tab;
    }
    
    /**
     * Adds to count, and if table is too small and not already resizing, initiates transfer.
     * If already resizing, helps perform transfer if work is available.
     * Rechecks occupancy after a transfer to see if another resize is already needed because resizings are lagging additions.
     * Map中的元素数据量累加方法：有额外的以下功能
     * 1.统计当前table一共有多少数据
     * 2.并判断是否达到扩容阈值标准，触发扩容
     * @param x     the count to add
     * @param check if <0, don't check resize, if <= 1 only check if uncontended
     */
    private final void addCount(long x, int check) {
        // as 表示 LongAdder.cells
        // b 表示LongAdder.base
        // s 表示当前map.table中元素的数量
        CounterCell[] cs;
        long b, s;

        // -------------------------统计当前table一共有多少数据----------------------------------
        // CASE1:
        // (as = counterCells) != null
        // 条件一：true->表示cells已经初始化了，当前线程应该去使用hash寻址找到合适的cell 去累加数据
        //        false->表示当前线程应该直接将数据累加到base（没有线程竞争）
        // !U.compareAndSwapLong(this, BASECOUNT, b = baseCount, s = b + x)
        // 条件二：false->表示写base成功，数据累加到base中了，当前竞争不激烈，不需要创建cells
        //        true->表示写base失败，与其他线程在base上发生了竞争，当前线程应该去尝试创建cells。
        if ((cs = counterCells) != null || !U.compareAndSetLong(this, BASECOUNT, b = baseCount, s = b + x)) {
            // 有几种情况进入到if块中？
            // 条件一为true->表示cells已经初始化了，当前线程应该去使用hash寻址找到合适的cell去累加数据
            // 条件二为true->表示写base失败，与其他线程在base上发生了竞争，当前线程应该去尝试创建cells。

            // a 表示当前线程hash寻址命中的cell
            CounterCell c;
            // v 表示当前线程写cell时的期望值
            long v;
            // m 表示当前cells数组的长度
            int m;
            // true -> 未发生线程竞争  false->发生线程竞争
            boolean uncontended = true;
            // ---------------------------------------------------------------------------
            // CASE2:
            // 条件一：as == null || (m = as.length - 1) < 0
            // true-> 表示当前线程是通过写base竞争失败（CASE1的条件二），然后进入的if块，就需要调用fullAddCount方法去扩容或者重试..
            // （fullAddCount方法就类似于LongAdder.longAccumulate方法）
            // 条件二：a = as[ThreadLocalRandom.getProbe() & m]) == null 前置条件：cells已经初始化了
            // true->表示当前线程命中的cell表格是个空的，需要当前线程进入fullAddCount方法去初始化cell，放入当前位置.
            // 条件三：!(uncontended = U.compareAndSwapLong(a, CELLVALUE, v = a.value, v + x)
            // 前置条件：条件二中当前线程命中的cell表格不是空的~
            //       false->取反得到false，表示当前线程使用cas方式更新当前命中的cell成功
            //       true->取反得到true,表示当前线程使用cas方式更新当前命中的cell失败，需要进入fullAddCount进行重试或者扩容cells。
            if (cs == null || (m = cs.length - 1)<0 || (c = cs[ThreadLocalRandom.getProbe() & m]) == null || !(uncontended = U.compareAndSetLong(c, CELLVALUE, v = c.value, v + x))) {
                // 考虑到fullAddCount里面的事情比较累，就让当前线程不参与到扩容相关的逻辑了，直接返回到调用点。
                fullAddCount(x, uncontended);
                return;
            }
            
            if (check <= 1) {
                return;
            }
            // sumCount统计当前散列表元素个数sum = base + cells[0] + ... + cells[n]，这是一个期望值
            s = sumCount();
        }

        // -------------------------判断是否达到扩容阈值标准，触发扩容----------------------------
        // CASE3:
        // check >= 0表示一定是一个put操作调用的addCount，check < 0是remove操作调用的addCount方法
        if (check >= 0) {
            // tab 表示 map.table
            // nt 表示 map.nextTable
            // n 表示map.table数组的长度
            // sc 表示sizeCtl的临时值
            Node<K, V>[] tab, nt;
            int n, sc;

            /**
             * sizeCtl < 0
             * 1. -1 表示当前table正在初始化（有线程在创建table数组），当前线程需要自旋等待..
             * 2.表示当前table数组正在进行扩容 ,高16位表示：扩容的标识戳   低16位表示：（1 + nThread） 当前参与并发扩容的线程数量
             *
             * sizeCtl = 0，表示创建table数组时 使用DEFAULT_CAPACITY为大小
             *
             * sizeCtl > 0
             *
             * 1. 如果table未初始化，表示初始化大小
             * 2. 如果table已经初始化，表示下次扩容时的 触发条件（阈值）
             */

            // 有条件自旋~
            // 条件一：s >= (long)(sc = sizeCtl)
            //        true -> 1.当前sizeCtl为一个负数 表示正在扩容中..
            //                2.当前sizeCtl是一个正数，表示扩容阈值，但是s已经达到扩容阈值（需要扩容）
            //        false -> 表示当前table尚未达到扩容阈值条件（不需要扩容）
            // 条件二：(tab = table) != null 恒成立 true
            // 条件三：(n = tab.length) < MAXIMUM_CAPACITY
            //        true -> 当前table长度小于最大值限制，则可以进行扩容。
            while (s >= (long) (sc = sizeCtl)
                    && (tab = table) != null
                    && (n = tab.length) < MAXIMUM_CAPACITY) {
                // 获取扩容唯一标识戳
                // eg: 16 -> 32 扩容标识戳为：1000 0000 0001 1011
                // 什么意思呢？
                // 即，所有将map容量由16扩容到32的线程，其拿到的扩容唯一标识戳都是1000 0000 0001 1011
                int rs = resizeStamp(n);
                // JDK16 最新的版本：resizeStamp 计算出来扩容标志戳
                // 00000000 00000000 1000 0000 0001 1011
                // resizeStamp(n) << RESIZE_STAMP_SHIFT = 1000 0000 0001 1011 00000000 00000000
                // rs = 10000000 00011011 00000000 00000000
                // int rs = resizeStamp(n) << RESIZE_STAMP_SHIFT;


                // --------------------------------------------------------------------------
                // CASE4:
                // 条件成立：表示当前table正在扩容，则，当前线程理论上应该协助table完成扩容
                if (sc < 0) {
                    // --------------------------------------------------------------
                    // CASE2: 条件1~4只要有个为true就会跳出循环，不会继续扩容~
                    // 条件一：(sc >>> RESIZE_STAMP_SHIFT) != rs
                    //       true -> 说明当前线程获取到的扩容唯一标识戳 非 本批次扩容
                    //       false -> 说明当前线程获取到的扩容唯一标识戳 是 本批次扩容
                    // 条件二：JDK1.8 中有bug,jira已经提出来了,其实想表达的是 sc == (rs << 16 ) + 1
                    //        true -> 表示扩容完毕，当前线程不需要再参与进来了
                    //        false -> 扩容还在进行中，当前线程可以参与
                    // 条件三：JDK1.8 中有bug,jira已经提出来了,其实想表达的是:
                    // sc == (rs << 16) + MAX_RESIZERS
                    //        true-> 表示当前参与并发扩容的线程达到了最大值 65535 - 1
                    //        false->表示当前线程可以参与进来
                    // 条件四：(nt = nextTable) == null
                    //        true -> 表示本次扩容结束
                    //        false -> 扩容正在进行中
                    if ((sc >>> RESIZE_STAMP_SHIFT) != rs
                            || sc == rs + 1
                            || sc == rs + MAX_RESIZERS
                            || (nt = nextTable) == null
                            || transferIndex <= 0) {
                        // 条件1~4只要有个为true就会跳出循环，不会继续扩容~
                        break;
                    }
                    // --------------------------------------------------------------
                    // CASE5:
                    // 前置条件：当前table正在执行扩容中（即，CASE4没有被通过）当前线程有机会参与进扩容。
                    // 条件成立：说明当前线程成功参与到扩容任务中，并且将sc低16位值加1，表示多了一个线程参与工作~
                    // 条件失败：
                    // 1.当前有很多线程都在此处尝试修改sizeCtl，有其它一个线程修改成功了
                    // 导致你的sc期望值与内存中的值不一致，CAS修改失败。(下次自选大概率不会在来到这里~)
                    // 2.transfer任务内部的线程也修改了sizeCtl。
                    if (U.compareAndSetInt(this, SIZECTL, sc, sc + 1)) {
                        // 扩容（迁移数据）：协助扩容线程，持有nextTable参数，进入该方法协助扩容~
                        transfer(tab, nt);
                    }
                }

                // --------------------------------------------------------------------------
                // CASE6: 以CAS的方式去更新sc，更新成功返回true，否则返回false
                // 条件成立，说明当前线程是触发扩容的**第一个**线程，在transfer方法需要做一些扩容准备工作:
                // rs << RESIZE_STAMP_SHIFT：将扩容唯一标识戳左移16位 eg:
                // 1000 0000 0001 1011 << 16 得到 1000 0000 0001 1011 0000 0000 0000 0000
                // 紧接这 (rs << RESIZE_STAMP_SHIFT) + 2)操作：
                // 1000 0000 0001 1011 0000 0000 0000 0000 + 2
                // => 1000 0000 0001 1011 0000 0000 0000 0010，这个二进制数有如下含义:
                // sizeCtl的高16位: 1000 0000 0001 1011 表示当前的扩容标识戳
                // sizeCtl的低16位: 0000 0000 0000 0010 表示(1 + nThread)，即，目前有多少个线程正在参与扩容~
                // 那么这里的n是怎么来的呢？
                // eg: (rs << RESIZE_STAMP_SHIFT) + 2 这里的2，就是1 + 1，后面的1就是对1*Thread，即(1+1*Threads)
                else if(U.compareAndSetInt(this, SIZECTL, sc, (rs << RESIZE_STAMP_SHIFT) + 2)) {
                    // CAS 将 sizeCtl 修改为 扩容标志戳 << 16 相当于留下地位去掉高位 10000000 00000000 + 2 = 10000000 000000010
                    // 然后开始扩容，第一个扩容的线程新的 table 还没创建出来，所以 nextTab 为空
                    transfer(tab, null);
                }
                // 重新计算table中的元素个数
                s = sumCount();
            }
        }
    }
    
    /**
     * Tries to presize table to accommodate the given number of elements.
     *
     * @param size number of elements (doesn't need to be perfectly accurate)
     */
    // 尝试调整哈希数组的大小，以容纳指定数量的元素
    private final void tryPresize(int size) {
        // 预备扩容到的目标容量
        int cap = (size >= (MAXIMUM_CAPACITY >>> 1)) ? MAXIMUM_CAPACITY                          // 如果哈希数组容量已经为最大容量的一半，则直接使用最大容量
            : tableSizeFor(size + (size >>> 1) + 1);    // 理想情形下，哈希数组容量增加0.5倍
        
        int sc;
        
        while((sc = sizeCtl) >= 0) {
            Node<K, V>[] tab = table;
            
            int len;
            
            // 如果哈希数组还未初始化，或者容量无效，则需要初始化一个哈希数组
            if(tab == null || (len = tab.length) == 0) {
                // 确定待扩容的新容量
                len = Math.max(sc, cap);
                
                // 原子地将sizeCtl字段更新为-1，代表当前Map进入了初始化哈希数组的阶段
                if(U.compareAndSetInt(this, SIZECTL, sc, -1)) {
                    try {
                        if(table == tab) {
                            @SuppressWarnings("unchecked")
                            Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[len];
                            table = nt;
                            
                            // 确定容量阙值为0.75*容量
                            sc = len - (len >>> 2);
                        }
                    } finally {
                        // 恢复sizeCtl标记为非负数
                        sizeCtl = sc;
                    }
                }
                
                // 在哈希数组已经初始化的情形下：如果预备扩容到的目标容量小于阙值(无需扩容)，或者哈希数组当前容量已达上限(无法扩容)，直接退出
            } else if(cap<=sc || len >= MAXIMUM_CAPACITY) {
                break;
                
                // 如果需要扩容
            } else if(tab == table) {
                int stamp = resizeStamp(len) << RESIZE_STAMP_SHIFT;
                
                // 原子地更新sizeCtl为
                if(U.compareAndSetInt(this, SIZECTL, sc, stamp + 2)) {
                    transfer(tab, null);
                }
            }
        }
    }
    
    /**
     * Moves and/or copies the nodes in each bin to new table. See above for explanation.
     */
    // 在哈希数组的扩容过程中进行数据迁移
    private final void transfer(Node<K, V>[] tab, Node<K, V>[] nextTab) {
        // n 表示扩容之前table数组的长度
        // stride 表示分配给线程任务的步长
        int n = tab.length;
        // NCPU = 12, n = 16 n >>> 3 = 2
        // 2 / 12 = 0;
        int stride = (NCPU>1) ? (n >>> 3) / NCPU : n;
        // stride = 16
        if (stride < MIN_TRANSFER_STRIDE) {
            stride = MIN_TRANSFER_STRIDE; // subdivide range
        }
        // nextTab 新 table
        // CASE0：nextTab == null
        // 条件成立：表示当前线程为触发本次扩容的线程，需要做一些扩容准备工作：(在if代码块中)
        // 条件不成立：表示当前线程是协助扩容的线程...
        if (nextTab == null) {            // initiating
            try {
                // 创建一个比扩容之前容量n大一倍的新table
                @SuppressWarnings("unchecked")
                Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[n << 1];
                nextTab = nt;
            } catch (Throwable ex) {      // try to cope with OOME
                sizeCtl = Integer.MAX_VALUE;
                return;
            }
            // 赋值nextTab对象给 nextTable ，方便协助扩容线程 拿到新表
            nextTable = nextTab;
            // 记录迁移数据整体位置的一个标记，初始值是原table数组的长度。
            // 可以理解为：全局范围内散列表的数据任务处理到哪个桶的位置了
            transferIndex = n;
        }
        // 转移之后作为一个标志位 MOVE
        // fwd节点，当某个桶位数据迁移处理完毕后，将此桶位设置为fwd节点，其它写线程或读线程看到后，会有不同逻辑。fwd结点指向新表nextTab的引用
        ForwardingNode<K, V> fwd = new ForwardingNode<K, V>(nextTab);
        // 表示新数组的长度
        int nextn = nextTab.length;
        // 标志当前线程到底需不需要继续往前去迁移数据
        boolean advance = true;
        // 当前线程任务结束了，但是不代表其他线程可以结束
        boolean finishing = false; // 确保在提交 nextTab 之前进行扫描

        // i 表示分配给当前线程的数据迁移任务，任务执行到的桶位下标（任务进度~表示当前线程的任务已经干到哪里了~）
        // bound 表示分配给当前线程任务的下界限制。（线程的数据迁移任务先从高位开始迁移，迁移到下界位置结束）
        int i = 0;// 转移的头结点
        int bound = 0;// 转移的尾节点
        // 自旋~ 非常长的一个for循环...
        while (true) {
            // f 桶位的头结点
            // fh 头结点的hash
            Node<K, V> f;
            int fh;
            /**
             * while循环的任务如下：(循环的条件为推进标记advance为true)
             * 1.给当前线程分配任务区间
             * 2.维护当前线程任务进度（i 表示当前处理的桶位）
             * 3.维护map对象全局范围内的进度
             */
            // 整个while循环就是在算i的值，过程太复杂，不用太关心
            // i的值会从n-1依次递减，感兴趣的可以打下断点就知道了
            // 其中n是旧桶数组的大小，也就是说i从15开始一直减到1这样去迁移元素
            // 利用 CAS + Volatile 控制不同的线程并发之后可以获取不到不同的工作区域
            // 比如线程A负责数组下标0-8的迁移工作
            // 线程B 负责数组下标9-16的迁移工作
            while (advance) {
                // nextIndex~nextBound分配任务的区间：
                // 分配任务的开始下标
                // 分配任务的结束下标
                int nextIndex;
                int nextBound;
                // -----------------------------------------------------------------------
                // CASE1:
                // 条件一：--i >= bound
                // 成立：表示当前线程的任务尚未完成，还有相应的区间的桶位要处理，--i 就让当前线程处理下一个桶位.
                // 不成立：表示当前线程任务已完成 或者 未分配
                if (--i >= bound || finishing) {
                    // 推进标记设置为 false
                    advance = false;

                // -----------------------------------------------------------------------
                // CASE2: (nextIndex = transferIndex) <= 0
                // transferIndex：可以理解为，全局范围内散列表的数据任务处理到哪个桶的位置了~
                // 前置条件：当前线程任务已完成 或 者未分配，即没有经过CASE1
                // 条件成立：表示对象全局范围内的桶位都分配完毕了，没有区间可分配了，设置当前线程的i变量为-1 跳出循环，然后执行退出迁移任务相关的程序
                // 条件不成立：表示对象全局范围内的桶位尚未分配完毕，还有区间可分配~
                } else if((nextIndex = transferIndex) <= 0) {
                    i = -1;
                    // 推进标记设置为 false
                    advance = false;

                // -----------------------------------------------------------------------
                // CASE3，其实就是移动i的一个过程：CAS更新成功，则i从当前位置-1，再复习一下i的含义：
                // i 表示分配给当前线程的数据迁移任务，任务执行到的桶位下标（任务进度~表示当前线程的任务已经干到哪里了~）
                // CASE3前置条件（未经过CASE1-2）：1、当前线程需要分配任务区间  2.全局范围内还有桶位尚未迁移
                // 条件成立：说明给当前线程分配任务成功
                // 条件失败：说明分配任务给当前线程失败，应该是和其它线程发生了竞争~
                } else if(U.compareAndSetInt(this, TRANSFERINDEX, nextIndex,
                        nextBound = (nextIndex > stride ? nextIndex - stride : 0))) {
                    bound = nextBound;
                    i = nextIndex - 1;
                    advance = false;
                }
            }
            /**
             处理线程任务完成后，线程退出transfer方法的逻辑：
             **/
            // -------------------------------------------------------------------------
            // CASE4：
            // 条件一：i < 0
            // 成立：表示当前线程未分配到任务，或已完成了任务
            // 条件二、三：一般情况下不会成里~
            if (i < 0 || i >= n || i + n >= nextn) {
                // 如果一次遍历完成了
                // 也就是整个map所有桶中的元素都迁移完成了

                // 保存sizeCtl的变量
                int sc;
                // 扩容结束条件判断
                if (finishing) {
                    // 如果全部桶中数据迁移完成了，则替换旧桶数组
                    // 并设置下一次扩容门槛为新桶数组容量的0.75倍
                    nextTable = null;
                    table = nextTab;
                    sizeCtl = (n << 1) - (n >>> 1);
                    return;
                }
                // -------------------------------------------------------------------------
                // CASE5：当前线程扩容完成，把并发扩容的线程数-1，该操作基于CAS，修改成功返回true
                // 条件成立：说明，更新 sizeCtl低16位 -1 操作成功，当前线程可以正常退出了~
                // 如果条件不成立：说明CAS更新操作时，与其他线程发生竞争了~
                if (U.compareAndSetInt(this, SIZECTL, sc = sizeCtl, sc - 1)) {

                    int stamp = resizeStamp(n) << RESIZE_STAMP_SHIFT;
                    // 条件成立：说明当前线程不是最后一个退出transfer任务的线程
                    // eg:
                    // 1000 0000 0001 1011 0000 0000 0000 0000
                    if ((sc - 2) != stamp) {
                        // 扩容完成两边肯定相等
                        // 正常退出
                        return;
                    }
                    // 完成标记finishing置为true，，finishing为true才会走到上面的if扩容结束条件判断
                    // 推进标记advance置为true
                    finishing = advance = true;
                    // i重新赋值为n
                    // 这样会再重新遍历一次桶数组，看看是不是都迁移完成了
                    // 也就是第二次遍历都会走到下面的(fh = f.hash) == MOVED这个条件
                    i = n; // recheck before commit
                }
            }

            /**
             线程处理一个桶位数据的迁移工作，处理完毕后，
             设置advance为true: 表示继续推荐，然后就会回到for，继续循环
             **/
            // -------------------------------------------------------------------------
            // CASE6:
            // 【CASE6~CASE8】前置条件：当前线程任务尚未处理完，正在进行中!
            // 条件成立：说明当前桶位未存放数据，只需要将此处设置为fwd节点即可。
            else if((f = tabAt(tab, i)) == null) {
                // 如果桶中无数据，直接放入FWD，标记该桶已迁移：
                // casTabAt通过CAS的方式去向Node数组指定位置i设置节点值，设置成功返回true，否则返回false
                // 即：将tab数组下标为i的结点设置为FWD结点
                advance = casTabAt(tab, i, null, fwd);
            }

            // -------------------------------------------------------------------------
            // CASE7: (fh = f.hash) == MOVED 如果桶中第一个元素的hash值为MOVED
            // 条件成立：说明头节f它是ForwardingNode节点,
            // 则，当前桶位已经迁移过了，当前线程不用再处理了，直接再次更新当前线程任务索引，再次处理下一个桶位 或者 其它操作~
            else if((fh = f.hash) == MOVED) {
                advance = true; // already processed
            }

            // -------------------------------------------------------------------------
            // CASE8:
            // 前置条件：**当前桶位有数据**，而且node节点 不是 fwd节点，说明这些数据需要迁移。
            else {
                // 锁定该桶并迁移元素：（sync 锁加在当前桶位的头结点）
                synchronized(f) {
                    // 再次判断当前桶第一个元素是否有修改，（可能出现其它线程抢先一步迁移/修改了元素）
                    // 防止在你加锁头对象之前，当前桶位的头对象被其它写线程修改过，导致你目前加锁对象错误...
                    if (tabAt(tab, i) == f) {
                        // 把一个链表拆分成两个链表（规则按照是桶中各元素的hash与桶大小n进行与操作）：
                        // 等于0的放到低位链表(low)中，不等于0的放到高位链表(high)中
                        // 其中低位链表迁移到新桶中的位置相对旧桶不变
                        // 高位链表迁移到新桶中位置正好是其在旧桶的位置加n
                        // 这也正是为什么扩容时容量在变成两倍的原因 （链表迁移原理参考上面的图）

                        // ln 表示低位链表引用
                        // hn 表示高位链表引用
                        Node<K, V> ln, hn;
                        // ---------------------------------------------------------------
                        // CASE9:
                        // 条件成立：表示当前桶位是链表桶位
                        if (fh >= 0) {
                            // 第一个元素的hash值大于等于0，说明该桶中元素是以链表形式存储的
                            // 这里与HashMap迁移算法基本类似，唯一不同的是多了一步寻找lastRun
                            // 这里的lastRun是提取出链表后面不用处理再特殊处理的子链表
                            // 比如所有元素的hash值与桶大小n与操作后的值分别为 0 0 4 4 0 0 0
                            // 则最后后面三个0对应的元素肯定还是在同一个桶中
                            // 这时lastRun对应的就是倒数第三个节点

                            // lastRun机制：
                            // 可以获取出 当前链表 末尾连续高位不变的 node
                            int runBit = fh & n;
                            Node<K, V> lastRun = f;
                            for (Node<K, V> p = f.next; p != null; p = p.next) {
                                int b = p.hash & n;
                                if(b != runBit) {
                                    runBit = b;
                                    lastRun = p;
                                }
                            }

                            // 看看最后这几个元素归属于低位链表还是高位链表
                            // 条件成立：说明lastRun引用的链表为 低位链表，那么就让 ln 指向 低位链表
                            if (runBit == 0) {
                                ln = lastRun;
                                hn = null;
                            }
                            // 否则，说明lastRun引用的链表为 高位链表，就让 hn 指向 高位链表
                            else {
                                hn = lastRun;
                                ln = null;
                            }
                            // 遍历链表，把hash&n为0的放在低位链表中,不为0的放在高位链表中
                            // 循环跳出条件：当前循环结点!=lastRun
                            for (Node<K, V> p = f; p != lastRun; p = p.next) {
                                int ph = p.hash;
                                K pk = p.key;
                                V pv = p.val;
                                // ph & n == 0 这个就是为什么扩容必须要2的倍数原因之一了
                                // n 是老表的大小，假设为 16 == 10000
                                // 那么与操作之后的效果要么就是 0 要么就是非 0了
                                if ((ph & n) == 0) {
                                    ln = new Node<K, V>(ph, pk, pv, ln);
                                } else {
                                    hn = new Node<K, V>(ph, pk, pv, hn);
                                }
                            }
                            
                            // nextTab[i]=ln
                            // 低位链表的位置不变
                            setTabAt(nextTab, i, ln);
                            
                            // nextTab[i+n]=hn
                            // 高位链表的位置是：原位置 + n
                            setTabAt(nextTab, i + n, hn);
                            
                            // tab[i]=fwd
                            // 标记当前桶已迁移
                            setTabAt(tab, i, fwd);

                            // advance为true，返回上面进行--i操作
                            advance = true;
                        }

                        // ---------------------------------------------------------------
                        // CASE10:
                        // 条件成立：表示当前桶位是 红黑树 代理结点TreeBin
                        else if (f instanceof TreeBin) {
                            // 如果第一个元素是树节点，也是一样，分化成两颗树
                            // 也是根据hash&n为0放在低位树中，不为0放在高位树中

                            // 转换头结点为 treeBin引用 t
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            // 低位双向链表 lo 指向低位链表的头  loTail 指向低位链表的尾巴
                            TreeNode<K, V> lo = null, loTail = null;
                            // 高位双向链表 lo 指向高位链表的头  loTail 指向高位链表的尾巴
                            TreeNode<K, V> hi = null, hiTail = null;

                            // lc 表示低位链表元素数量
                            // hc 表示高位链表元素数量
                            int lc = 0, hc = 0;

                            // 遍历整颗树(TreeBin中的双向链表，从头结点至尾节点)，根据hash&n是否为0分化成两颗树：
                            for (Node<K, V> e = t.first; e != null; e = e.next) {
                                // h 表示循环处理当前元素的 hash
                                int h = e.hash;
                                // 使用当前节点 构建出来的新的TreeNode
                                TreeNode<K, V> p = new TreeNode<K, V>(h, e.key, e.val, null, null);

                                // ---------------------------------------------------
                                // CASE11:
                                // 条件成立：表示当前循环节点 属于低位链节点
                                if((h & n) == 0) {
                                    // 条件成立：说明当前低位链表还没有数据
                                    if ((p.prev = loTail) == null) {
                                        lo = p;
                                    }
                                    // 说明低位链表已经有数据了，此时当前元素追加到低位链表的末尾就行了
                                    else {
                                        loTail.next = p;
                                    }
                                    // 将低位链表尾指针指向 p 节点
                                    loTail = p;
                                    ++lc;
                                }
                                // ---------------------------------------------------
                                // CASE12:
                                // 条件成立：当前节点属于高位链节点
                                else {
                                    if((p.prev = hiTail) == null) {
                                        hi = p;
                                    } else {
                                        hiTail.next = p;
                                    }
                                    hiTail = p;
                                    ++hc;
                                }
                            }
                            // 如果分化的树中元素个数小于等于6，则退化成链表
                            ln = (lc<=UNTREEIFY_THRESHOLD) ? untreeify(lo) : (hc != 0) ? new TreeBin<K, V>(lo) : t;
                            
                            hn = (hc<=UNTREEIFY_THRESHOLD) ? untreeify(hi) : (lc != 0) ? new TreeBin<K, V>(hi) : t;
                            
                            // nextTab[i]=ln
                            // 低位树的位置不变
                            setTabAt(nextTab, i, ln);
                            
                            // nextTab[i+n]=hn
                            // 高位树的位置是原位置加n
                            setTabAt(nextTab, i + n, hn);
                            
                            // tab[i]=fwd
                            // 标记该桶已迁移
                            setTabAt(tab, i, fwd);

                            // advance为true，返回上面进行--i操作
                            advance = true;
                        }
                    }
                }
            }

        } // while (true) 外部大循环结束
    }
    
    
    /* ---------------- Counter support -------------- */
    
    final long sumCount() {
        CounterCell[] cs = counterCells;
        
        long sum = baseCount;
        
        if(cs != null) {
            for(CounterCell c : cs) {
                if(c != null) {
                    sum += c.value;
                }
            }
        }
        
        return sum;
    }
    
    // See LongAdder version for explanation
    private final void fullAddCount(long x, boolean wasUncontended) {
        int h;
        
        if((h = ThreadLocalRandom.getProbe()) == 0) {
            ThreadLocalRandom.localInit();      // force initialization
            h = ThreadLocalRandom.getProbe();
            wasUncontended = true;
        }
        
        boolean collide = false;                // True if last slot nonempty
        
        while(true) {
            CounterCell[] cs;
            CounterCell c;
            int n;
            long v;
            
            if((cs = counterCells) != null && (n = cs.length)>0) {
                if((c = cs[(n - 1) & h]) == null) {
                    if(cellsBusy == 0) {            // Try to attach new Cell
                        CounterCell r = new CounterCell(x); // Optimistic create
                        if(cellsBusy == 0 && U.compareAndSetInt(this, CELLSBUSY, 0, 1)) {
                            boolean created = false;
                            try {               // Recheck under lock
                                CounterCell[] rs;
                                int m, j;
                                if((rs = counterCells) != null && (m = rs.length)>0 && rs[j = (m - 1) & h] == null) {
                                    rs[j] = r;
                                    created = true;
                                }
                            } finally {
                                cellsBusy = 0;
                            }
                            
                            if(created) {
                                break;
                            }
                            
                            continue;           // Slot is now non-empty
                        }
                    }
                    
                    collide = false;
                    
                    // CAS already known to fail
                } else if(!wasUncontended) {
                    wasUncontended = true;      // Continue after rehash
                } else if(U.compareAndSetLong(c, CELLVALUE, v = c.value, v + x)) {
                    break;
                } else if(counterCells != cs || n >= NCPU) {
                    collide = false;            // At max size or stale
                } else if(!collide) {
                    collide = true;
                } else if(cellsBusy == 0 && U.compareAndSetInt(this, CELLSBUSY, 0, 1)) {
                    try {
                        // Expand table unless stale
                        if(counterCells == cs) {
                            counterCells = Arrays.copyOf(cs, n << 1);
                        }
                    } finally {
                        cellsBusy = 0;
                    }
                    collide = false;
                    continue;                   // Retry with expanded table
                }
                
                h = ThreadLocalRandom.advanceProbe(h);
            } else if(cellsBusy == 0 && counterCells == cs && U.compareAndSetInt(this, CELLSBUSY, 0, 1)) {
                boolean init = false;
                
                try {                           // Initialize table
                    if(counterCells == cs) {
                        CounterCell[] rs = new CounterCell[2];
                        rs[h & 1] = new CounterCell(x);
                        counterCells = rs;
                        init = true;
                    }
                } finally {
                    cellsBusy = 0;
                }
                
                if(init) {
                    break;
                }
            } else if(U.compareAndSetLong(this, BASECOUNT, v = baseCount, v + x)) {
                break;                          // Fall back on using base
            }
        }
    }
    
    
    /* ---------------- Conversion from/to TreeBins -------------- */
    
    /**
     * Replaces all linked nodes in bin at given index unless table is too small, in which case resizes instead.
     */
    /*
     * 观察哈希槽（链）上处于波动期的元素，以决定下一步是扩容还是将链表转换为红黑树
     *
     * tab：待转换的链表
     * hash：某元素的哈希值
     */
    private final void treeifyBin(Node<K, V>[] tab, int index) {
        if (tab == null) {
            return;
        }
        // b：
        // n: tab的长度
        // sc: sizeCtl
        Node<K, V> b;
        int n;

        // 哈希数组的容量还未达到形成一棵红黑树的最低要求
        // ---------------------------------------------------------------------------
        // CASE1:
        // 条件成立：说明当前table数组长度未达到 64，此时不进行树化操作，而进行扩容操作。
        if ((n = tab.length)<MIN_TREEIFY_CAPACITY) {
            // 尝试调整哈希数组的大小，以容纳指定数量的元素（默认增加一倍）
            // table进行扩容
            tryPresize(n << 1);
        }
        // ---------------------------------------------------------------------------
        // CASE2:
        // 条件成立：说明当前桶位有数据，且是普通node数据。
        else {
            // 获取tab[index]
            b = tabAt(tab, index);
            if (b == null || b.hash < 0) {
                return;
            }
            // 给头元素b加锁
            synchronized(b) {
                // 双重检查机制
                // 条件成立：表示加锁没问题，b没有被其他线程修改过
                if (tabAt(tab, index) == b) {
                    // 下面的for循环逻辑，目的就是把桶位中的单链表转换成双向链表，便于树化~
                    // hd指向双向列表的头部，tl指向双向链表的尾部
                    TreeNode<K, V> hd = null, tl = null;
                    
                    // 1.首先，将所有普通结点“转换”为红黑树结点并串联起来
                    for(Node<K, V> e = b; e != null; e = e.next) {
                        
                        TreeNode<K, V> p = new TreeNode<>(e.hash, e.key, e.val, null, null);
                        
                        if((p.prev = tl) == null) {
                            hd = p;
                        } else {
                            tl.next = p;
                        }
                        
                        tl = p;
                    }
                    
                    // 2.其次，创建红黑树，即把所有红黑树结点安置在树中合适的位置上
                    TreeBin<K, V> treeBin = new TreeBin<>(hd);
                    
                    // 3.最后，将红黑树设置到哈希槽上
                    setTabAt(tab, index, treeBin);
                }
            }
        }
    }
    
    /**
     * Returns a list of non-TreeNodes replacing those in given list.
     */
    static <K, V> Node<K, V> untreeify(Node<K, V> b) {
        Node<K, V> hd = null, tl = null;
        for(Node<K, V> q = b; q != null; q = q.next) {
            Node<K, V> p = new Node<>(q.hash, q.key, q.val);
            if(tl == null) {
                hd = p;
            } else {
                tl.next = p;
            }
            
            tl = p;
        }
        return hd;
    }
    
    /**
     * Computes initial batch value for bulk tasks.
     * The returned value is approximately exp2 of the number of times (minus one) to split task by two before executing leaf action.
     * This value is faster to compute and more convenient to use as a guide to splitting than is the depth,
     * since it is used while dividing by two anyway.
     */
    final int batchFor(long b) {
        long n;
        
        if(b == Long.MAX_VALUE || (n = sumCount())<=1L || n<b) {
            return 0;
        }
        
        int sp = ForkJoinPool.getCommonPoolParallelism() << 2; // slack of 4
        
        return (b>0L && (n /= b)<sp) ? (int) n : sp;
    }
    
    
    
    
    
    
    /**
     * Key-value entry.  This class is never exported out as a
     * user-mutable Map.Entry (i.e., one supporting setValue; see
     * MapEntry below), but can be used for read-only traversals used
     * in bulk tasks.  Subclasses of Node with a negative hash field
     * are special, and contain null keys and values (but are never
     * exported).  Otherwise, keys and vals are never null.
     */
    // ConcurrentHashMap中的普通结点信息，每个Node代表一个元素，里面包含了key和value的信息
    static class Node<K, V> implements Map.Entry<K, V> {
        // hash值
        final int hash;
        // key
        final K key;
        // value
        volatile V val;
        // 后驱节点
        volatile Node<K, V> next;
        
        Node(int hash, K key, V val) {
            this.hash = hash;
            this.key = key;
            this.val = val;
        }
        
        Node(int hash, K key, V val, Node<K, V> next) {
            this(hash, key, val);
            this.next = next;
        }
        
        public final K getKey() {
            return key;
        }
        
        public final V getValue() {
            return val;
        }
        
        public final int hashCode() {
            return key.hashCode() ^ val.hashCode();
        }
        
        public final String toString() {
            return Helpers.mapEntryToString(key, val);
        }
        
        public final V setValue(V value) {
            throw new UnsupportedOperationException();
        }
        
        public final boolean equals(Object o) {
            Object k, v, u;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null && (v = e.getValue()) != null && (k == key || k.equals(key)) && (v == (u = val) || v.equals(u)));
        }
        
        /**
         * Virtualized support for map.get(); overridden in subclasses.
         */
        Node<K, V> find(int h, Object k) {
            Node<K, V> e = this;
            if(k != null) {
                do {
                    K ek;
                    if(e.hash == h && ((ek = e.key) == k || (ek != null && k.equals(ek)))) {
                        return e;
                    }
                } while((e = e.next) != null);
            }
            return null;
        }
    }
    
    /**
     * Nodes for use in TreeBins.
     */
    // ConcurrentHashMap中的红黑树结点
    static final class TreeNode<K, V> extends Node<K, V> {
        // 父节点
        TreeNode<K, V> parent;  // red-black tree links
        // 左子节点
        TreeNode<K, V> left;
        // 右节点
        TreeNode<K, V> right;
        // 节点有红、黑两种颜色~
        boolean red;
        // 前驱节点
        TreeNode<K, V> prev;    // needed to unlink next upon deletion
        
        
        // 仍然需要维护next链接
        TreeNode(int hash, K key, V val, Node<K, V> next, TreeNode<K, V> parent) {
            super(hash, key, val, next);
            this.parent = parent;
        }
        
        Node<K, V> find(int h, Object k) {
            return findTreeNode(h, k, null);
        }
        
        /**
         * Returns the TreeNode (or null if not found) for the given key
         * starting at given root.
         */
        // 根据给定的key和hash（由key计算而来）查找对应的（同位）元素，如果找不到，则返回null
        final TreeNode<K, V> findTreeNode(int h, Object k, Class<?> kc) {
            if (k != null) {
                TreeNode<K, V> p = this;
                
                do {
                    int ph, dir;
                    K pk;
                    TreeNode<K, V> q;
                    TreeNode<K, V> pl = p.left, pr = p.right;
                    if ((ph = p.hash)>h) {
                        p = pl;
                    }

                    else if (ph<h) {
                        p = pr;
                    }

                    else if ((pk = p.key) == k || (pk != null && k.equals(pk))) {
                        return p;
                    } else if(pl == null) {
                        p = pr;
                    } else if(pr == null) {
                        p = pl;
                    } else if((kc != null || (kc = comparableClassFor(k)) != null) && (dir = compareComparables(kc, k, pk)) != 0) {
                        p = (dir<0) ? pl : pr;
                    } else if((q = pr.findTreeNode(h, k, kc)) != null) {
                        return q;
                    } else {
                        p = pl;
                    }
                } while (p != null);
            }
            
            return null;
        }
        
    }
    
    /**
     * TreeNodes used at the heads of bins. TreeBins do not hold user
     * keys or values, but instead point to list of TreeNodes and
     * their root. They also maintain a parasitic read-write lock
     * forcing writers (who hold bin lock) to wait for readers (who do
     * not) to complete before tree restructuring operations.
     */
    // 红黑树(红黑树代理结点)
    static final class TreeBin<K, V> extends Node<K, V> {
        // values for lockState
        static final int WRITER = 1; // set while holding write lock 写锁状态
        static final int WAITER = 2; // set when waiting for write lock 等待者状态（写线程在等待）
        static final int READER = 4; // increment value for setting read lock 读锁状态

        // 链表的头节点
        volatile TreeNode<K, V> first;
        // 红黑树根节点
        TreeNode<K, V> root;
        
        volatile Thread waiter;
        /**
         * 锁的状态：
         * 1.写锁状态 写是独占状态，以散列表来看，真正进入到TreeBin中的写线程 同一时刻只能有一个线程。
         * 2.读锁状态 读锁是共享，同一时刻可以有多个线程 同时进入到 TreeBin对象中获取数据。 每一个线程 都会给 lockStat + 4
         * 3.等待者状态（写线程在等待），当TreeBin中有读线程目前正在读取数据时，写线程无法修改数据，那么就将lockState的最低2位设置为 0b 10 ：即，换算成十进制就是WAITER = 2;
         */
        volatile int lockState;
        
        private static final Unsafe U = Unsafe.getUnsafe();
        private static final long LOCKSTATE = U.objectFieldOffset(TreeBin.class, "lockState");
        
        
        
        /**
         * Creates bin with initial set of nodes headed by b.
         */
        // 创建红黑树，即把所有红黑树结点安置在树中合适的位置上
        TreeBin(TreeNode<K, V> n) {
            // 设置当前节点hash为-2 表示此节点是TreeBin节点
            super(TREEBIN, null, null);
            // 使用first 引用 treeNode链表
            this.first = n;
            // r 红黑树的根节点引用
            TreeNode<K, V> r = null;
            TreeNode<K, V> x = n;
            TreeNode<K, V> next;
            // x表示遍历的当前节点
            while (x != null) {
                next = (TreeNode<K, V>) x.next;
                // 强制设置当前插入节点的左右子树为null
                x.left = x.right = null;
                // ----------------------------------------------------------------------
                // CASE1：
                // 条件成立：说明当前红黑树是一个空树，那么设置插入元素为根节点
                // 第一次循环，r一定是null
                if (r == null) {
                    // 根节点的父节点 一定为 null
                    x.parent = null;
                    // 颜色改为黑色
                    x.red = false;
                    // 让r引用x所指向的对象。
                    r = x;
                }
                // ----------------------------------------------------------------------
                // CASE2：r != null
                else {
                    // 非第一次循环，都会来带else分支，此时红黑树根节点已经有数据了
                    // k 表示 插入节点的key
                    K k = x.key;
                    // h 表示 插入节点的hash
                    int h = x.hash;
                    // kc 表示 插入节点key的class类型
                    Class<?> kc = null;
                    // p 表示 为查找插入节点的父节点的一个临时节点
                    TreeNode<K, V> p = r;
                    // 这里的for循环，就是一个查找并插入的过程
                    while (true) {
                        // dir (-1, 1)
                        // -1 表示插入节点的hash值大于 当前p节点的hash
                        // 1 表示插入节点的hash值 小于 当前p节点的hash
                        // ph p表示 为查找插入节点的父节点的一个临时节点的hash
                        int dir, ph;
                        // 临时节点 key
                        K pk = p.key;
                        // 插入节点的hash值 小于 当前节点
                        if ((ph = p.hash) > h) {
                            // 插入节点可能需要插入到当前节点的左子节点 或者 继续在左子树上查找
                            dir = -1;
                        }
                        // 插入节点的hash值 大于 当前节点
                        else if (ph < h) {
                            // 插入节点可能需要插入到当前节点的右子节点 或者 继续在右子树上查找
                            dir = 1;
                        }
                        // 如果执行到 CASE3，说明当前插入节点的hash 与 当前节点的hash一致，会在case3 做出最终排序。最终
                        // 拿到的dir 一定不是0，（-1， 1）
                        else if ((kc == null
                                && (kc = comparableClassFor(k)) == null)
                                || (dir = compareComparables(kc, k, pk)) == 0) {
                            dir = tieBreakOrder(k, pk);
                        }

                        // xp 想要表示的是 插入节点的 父节点
                        TreeNode<K, V> xp = p;
                        // 条件成立：说明当前p节点 即为插入节点的父节点
                        // 条件不成立：说明p节点 底下还有层次，需要将p指向 p的左子节点 或者 右子节点，表示继续向下搜索。
                        if ((p = (dir<=0) ? p.left : p.right) == null) {
                            // 设置插入节点的父节点 为 当前节点
                            x.parent = xp;
                            // 小于P节点，需要插入到P节点的左子节点
                            if (dir <= 0) {
                                xp.left = x;
                                // 大于P节点，需要插入到P节点的右子节点
                            }

                            else {
                                xp.right = x;
                            }
                            // 插入节点后，红黑树性质 可能会被破坏，所以需要调用 平衡方法
                            r = balanceInsertion(r, x);
                            
                            break;
                        }
                    }// while(true)
                }
                x = next;
            }
            // 将r 赋值给 TreeBin对象的 root引用。
            this.root = r;
            assert checkInvariants(root);
        }
        
        
        
        /*▼ 插入/删除 ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓┓ */
        
        /**
         * Finds or adds a node.
         *
         * @return null if added
         */
        // 向当前红黑树中插入元素
        final TreeNode<K, V> putTreeVal(int h, K k, V v) {
            Class<?> kc = null;
            
            boolean searched = false;
            
            for(TreeNode<K, V> p = root; ; ) {
                int dir, ph;
                K pk;
                if(p == null) {
                    first = root = new TreeNode<K, V>(h, k, v, null, null);
                    break;
                } else if((ph = p.hash)>h) {
                    dir = -1;
                } else if(ph<h) {
                    dir = 1;
                } else if((pk = p.key) == k || (pk != null && k.equals(pk))) {
                    return p;
                } else if((kc == null && (kc = comparableClassFor(k)) == null) || (dir = compareComparables(kc, k, pk)) == 0) {
                    
                    if(!searched) {
                        TreeNode<K, V> q, ch;
                        searched = true;
                        if(((ch = p.left) != null && (q = ch.findTreeNode(h, k, kc)) != null) || ((ch = p.right) != null && (q = ch.findTreeNode(h, k, kc)) != null)) {
                            return q;
                        }
                    }
                    
                    dir = tieBreakOrder(k, pk);
                }
                
                TreeNode<K, V> xp = p;
                
                if((p = (dir<=0) ? p.left : p.right) == null) {
                    TreeNode<K, V> x, f = first;
                    
                    first = x = new TreeNode<K, V>(h, k, v, f, xp);
                    
                    if(f != null) {
                        f.prev = x;
                    }
                    
                    if(dir<=0) {
                        xp.left = x;
                    } else {
                        xp.right = x;
                    }
                    
                    if(!xp.red) {
                        x.red = true;
                    } else {
                        lockRoot();
                        try {
                            root = balanceInsertion(root, x);
                        } finally {
                            unlockRoot();
                        }
                    }
                    break;
                }
            }
            
            assert checkInvariants(root);
            
            return null;
        }
        
        /**
         * Removes the given node, that must be present before this
         * call.  This is messier than typical red-black deletion code
         * because we cannot swap the contents of an interior node
         * with a leaf successor that is pinned by "next" pointers
         * that are accessible independently of lock. So instead we
         * swap the tree linkages.
         *
         * @return true if now too small, so should be untreeified
         */
        // 将元素从红黑树中移除
        final boolean removeTreeNode(TreeNode<K, V> p) {
            TreeNode<K, V> next = (TreeNode<K, V>) p.next;
            TreeNode<K, V> pred = p.prev;  // unlink traversal pointers
            TreeNode<K, V> r, rl;
            
            if(pred == null) {
                first = next;
            } else {
                pred.next = next;
            }
            
            if(next != null) {
                next.prev = pred;
            }
            
            if(first == null) {
                root = null;
                return true;
            }
            if((r = root) == null || r.right == null || // too small
                (rl = r.left) == null || rl.left == null) {
                return true;
            }
            
            lockRoot();
            
            try {
                TreeNode<K, V> replacement;
                TreeNode<K, V> pl = p.left;
                TreeNode<K, V> pr = p.right;
                
                if(pl != null && pr != null) {
                    TreeNode<K, V> s = pr, sl;
                    
                    // find successor
                    while((sl = s.left) != null) {
                        s = sl;
                    }
                    
                    boolean c = s.red;
                    s.red = p.red;
                    p.red = c; // swap colors
                    TreeNode<K, V> sr = s.right;
                    TreeNode<K, V> pp = p.parent;
                    
                    if(s == pr) { // p was s's direct parent
                        p.parent = s;
                        s.right = p;
                    } else {
                        TreeNode<K, V> sp = s.parent;
                        if((p.parent = sp) != null) {
                            if(s == sp.left) {
                                sp.left = p;
                            } else {
                                sp.right = p;
                            }
                        }
                        
                        if((s.right = pr) != null) {
                            pr.parent = s;
                        }
                    }
                    
                    p.left = null;
                    if((p.right = sr) != null) {
                        sr.parent = p;
                    }
                    
                    if((s.left = pl) != null) {
                        pl.parent = s;
                    }
                    
                    if((s.parent = pp) == null) {
                        r = s;
                    } else if(p == pp.left) {
                        pp.left = s;
                    } else {
                        pp.right = s;
                    }
                    
                    if(sr != null) {
                        replacement = sr;
                    } else {
                        replacement = p;
                    }
                } else if(pl != null) {
                    replacement = pl;
                } else if(pr != null) {
                    replacement = pr;
                } else {
                    replacement = p;
                }
                
                if(replacement != p) {
                    TreeNode<K, V> pp = replacement.parent = p.parent;
                    if(pp == null) {
                        r = replacement;
                    } else if(p == pp.left) {
                        pp.left = replacement;
                    } else {
                        pp.right = replacement;
                    }
                    
                    p.left = p.right = p.parent = null;
                }
                
                root = (p.red) ? r : balanceDeletion(r, replacement);
                
                // detach pointers
                if(p == replacement) {
                    TreeNode<K, V> pp;
                    if((pp = p.parent) != null) {
                        if(p == pp.left) {
                            pp.left = null;
                        } else if(p == pp.right) {
                            pp.right = null;
                        }
                        
                        p.parent = null;
                    }
                }
            } finally {
                unlockRoot();
            }
            
            assert checkInvariants(root);
            
            return false;
        }
        
        // 将元素x插入到红黑树root后，可能会破坏其平衡性，所以这里需要做出调整，保持红黑树的平衡
        static <K, V> TreeNode<K, V> balanceInsertion(TreeNode<K, V> root, TreeNode<K, V> x) {
            x.red = true;
            
            TreeNode<K, V> xp, xpp, xppl, xppr;
            
            while(true) {
                if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }

                else if (!xp.red || (xpp = xp.parent) == null) {
                    return root;
                }
                
                if (xp == (xppl = xpp.left)) {
                    if((xppr = xpp.right) != null && xppr.red) {
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if(x == xp.right) {
                            root = rotateLeft(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        
                        if(xp != null) {
                            xp.red = false;
                            if(xpp != null) {
                                xpp.red = true;
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                } else {
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        
                        if (xp != null) {
                            xp.red = false;
                            if(xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }
        
        // 将元素x从红黑树root移除后，可能会破坏其平衡性，所以这里需要做出调整，保持红黑树的平衡
        static <K, V> TreeNode<K, V> balanceDeletion(TreeNode<K, V> root, TreeNode<K, V> x) {
            TreeNode<K, V> xp, xpl, xpr;
            
            while(true) {
                if (x == null || x == root) {
                    return root;
                }

                else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }

                else if (x.red) {
                    x.red = false;
                    return root;
                }

                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    
                    if (xpr == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) && (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }

                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null) {
                                    sl.red = false;
                                }
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ? null : xp.right;
                            }
                            
                            if (xpr != null) {
                                xpr.red = (xp != null) && xp.red;
                                if ((sr = xpr.right) != null) {
                                    sr.red = false;
                                }
                            }
                            
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            
                            x = root;
                        }
                    }
                }

                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    
                    if (xpl == null) {
                        x = xp;
                    }

                    else {
                        TreeNode<K, V> sl = xpl.left, sr = xpl.right;
                        if((sl == null || !sl.red) && (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        } else {
                            if(sl == null || !sl.red) {
                                if(sr != null) {
                                    sr.red = false;
                                }
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ? null : xp.left;
                            }
                            
                            if(xpl != null) {
                                xpl.red = (xp != null) && xp.red;
                                if((sl = xpl.left) != null) {
                                    sl.red = false;
                                }
                            }
                            
                            if(xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            
                            x = root;
                        }
                    }
                }
            }
        }
        
        // 左旋
        static <K, V> TreeNode<K, V> rotateLeft(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> r, pp, rl;
            
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null) {
                    rl.parent = p;
                }
                
                if ((pp = r.parent = p.parent) == null) {
                    (root = r).red = false;
                }

                else if(pp.left == p) {
                    pp.left = r;
                }

                else {
                    pp.right = r;
                }

                r.left = p;
                p.parent = r;
            }
            
            return root;
        }
        
        // 右旋
        static <K, V> TreeNode<K, V> rotateRight(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> l, pp, lr;
            
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null) {
                    lr.parent = p;
                }
                
                if ((pp = l.parent = p.parent) == null) {
                    (root = l).red = false;
                }

                else if(pp.right == p) {
                    pp.right = l;
                }

                else {
                    pp.left = l;
                }
                
                l.right = p;
                p.parent = l;
            }
            
            return root;
        }
        
        /*▲ 插入/删除 ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓┛ */
        
        
        
        /**
         * Tie-breaking utility for ordering insertions when equal
         * hashCodes and non-comparable. We don't require a total
         * order, just a consistent insertion rule to maintain
         * equivalence across rebalancings. Tie-breaking further than
         * necessary simplifies testing a bit.
         */
        // 用于红黑树元素比较
        static int tieBreakOrder(Object a, Object b) {
            int d;
            
            if(a == null
                || b == null
                || (d = a.getClass().getName().compareTo(b.getClass().getName())) == 0) {
                d = (System.identityHashCode(a)<=System.identityHashCode(b) ? -1 : 1);
            }
            
            return d;
        }
        
        /**
         * Returns matching node or null if none. Tries to search
         * using tree comparisons from root, but continues linear
         * search when lock not available.
         */
        // 根据给定的key和hash（由key计算而来）查找对应的（同位）元素，如果找不到，则返回null
        final Node<K, V> find(int hash, Object k) {
            if (k != null) {
                // e 表示循环迭代的当前节点：迭代的是first引用的链表
                for (Node<K, V> e = first; e != null; ) {
                    // s 保存的是lock临时状态
                    // ek 链表当前节点 的key
                    int s;
                    K ek;
                    // ----------------------------------------------------------------------
                    // CASE1：
                    // (WAITER|WRITER) => 0010 | 0001 => 0011
                    // lockState & 0011 != 0 条件成立：说明当前TreeBin有等待者线程 或者 目前有写操作线程正在加锁
                    if (((s = lockState) & (WAITER | WRITER)) != 0) {
                        if (e.hash == hash && ((ek = e.key) == k || (ek != null && k.equals(ek)))) {
                            return e;
                        }
                        e = e.next;
                    }
                    // ----------------------------------------------------------------------
                    // CASE2：
                    // 前置条件：当前TreeBin中 等待者线程 或者 写线程 都没有
                    // 条件成立：说明添加读锁成功
                    else if(U.compareAndSetInt(this, LOCKSTATE, s, s + READER)) {
                        TreeNode<K, V> r, p;
                        try {
                            // 查询操作
                            p = ((r = root) == null ? null : r.findTreeNode(hash, k, null));
                        } finally {
                            // w 表示等待者线程
                            Thread w;
                            // U.getAndAddInt(this, LOCKSTATE, -READER) == (READER|WAITER)
                            // 1.当前线程查询红黑树结束，释放当前线程的读锁 就是让 lockstate 值 - 4
                            // (READER|WAITER) = 0110 => 表示当前只有一个线程在读，且“有一个线程在等待”
                            // 当前读线程为 TreeBin中的最后一个读线程。

                            // 2.(w = waiter) != null 说明有一个写线程在等待读操作全部结束。
                            if (U.getAndAddInt(this, LOCKSTATE, -READER) == (READER | WAITER) && (w = waiter) != null) {
                                LockSupport.unpark(w);
                            }
                        }
                        return p;
                    }
                }
            }
            return null;
        }
        
        /**
         * Acquires write lock for tree restructuring.
         * 加锁：基于CAS的方式更新LOCKSTATE的值，期望值是0，更新值是WRITER（1，写锁）
         */
        private final void lockRoot() {
            if(!U.compareAndSetInt(this, LOCKSTATE, 0, WRITER)) {
                // 条件成立：说明lockState 并不是 0，说明此时有其它读线程在treeBin红黑树中读取数据。
                contendedLock(); // offload to separate method
            }
        }
        
        /**
         * Releases write lock for tree restructuring.
         * 释放锁
         */
        private final void unlockRoot() {
            // lockstate置为0
            lockState = 0;
        }
        
        /**
         * Possibly blocks awaiting root lock.
         */
        private final void contendedLock() {
            boolean waiting = false;
            // s表示lock值
            for(int s; ; ) {
                // ~WAITER = 11111....01
                // 条件成立：说明目前TreeBin中没有读线程在访问 红黑树
                // 条件不成立：有线程在访问红黑树
                if (((s = lockState) & ~WAITER) == 0) {
                    // 条件成立：说明写线程 抢占锁成功
                    if (U.compareAndSetInt(this, LOCKSTATE, s, WRITER)) {
                        if (waiting) {
                            // 设置TreeBin对象waiter 引用为null
                            waiter = null;
                        }
                        return;
                    }
                }

                // lock & 0000...10 = 0, 条件成立：说明lock 中 waiter 标志位 为0，此时当前线程可以设置为1了，然后将当前线程挂起。
                else if((s & WAITER) == 0) {
                    if (U.compareAndSetInt(this, LOCKSTATE, s, s | WAITER)) {
                        waiting = true;
                        waiter = Thread.currentThread();
                    }
                }

                // 条件成立：说明当前线程在CASE2中已经将 treeBin.waiter 设置为了当前线程，并且将lockState 中表示 等待者标记位的地方 设置为了1
                // 这个时候，就让当前线程 挂起。。
                else if (waiting) {
                    LockSupport.park(this);
                }
            }
        }
        
        /**
         * Checks invariants recursively for the tree of Nodes rooted at t.
         */
        static <K, V> boolean checkInvariants(TreeNode<K, V> t) {
            TreeNode<K, V> tp = t.parent, tl = t.left, tr = t.right, tb = t.prev, tn = (TreeNode<K, V>) t.next;
            
            if(tb != null && tb.next != t) {
                return false;
            }
            
            if(tn != null && tn.prev != t) {
                return false;
            }
            
            if(tp != null && t != tp.left && t != tp.right) {
                return false;
            }
            
            if(tl != null && (tl.parent != t || tl.hash>t.hash)) {
                return false;
            }
            
            if(tr != null && (tr.parent != t || tr.hash<t.hash)) {
                return false;
            }
            
            if(t.red && tl != null && tl.red && tr != null && tr.red) {
                return false;
            }
            
            if(tl != null && !checkInvariants(tl)) {
                return false;
            }
            
            return tr == null || checkInvariants(tr);
        }
        
    }
    
    
    
    /**
     * A node inserted at head of bins during transfer operations.
     */
    // 前向结点，应用在数据迁移中。比如Map在扩容时，会将新容器包裹在前向结点中，扩容完毕之后，则撤销该前向结点
    static final class ForwardingNode<K, V> extends Node<K, V> {
        // nextTable表示新散列表的引用
        final Node<K, V>[] nextTable;
        
        ForwardingNode(Node<K, V>[] tab) {
            super(MOVED, null, null);
            this.nextTable = tab;
        }
        // 到新表上去读数据
        Node<K, V> find(int h, Object k) {
            // loop to avoid arbitrarily deep recursion on forwarding nodes
outer:
            for (Node<K, V>[] tab = nextTable; ; ) {
                // n 表示为扩容而创建的新表的长度
                // e 表示在扩容而创建新表时，使用寻址算法得到的桶位头结点
                Node<K, V> e;
                int n;
                // 条件一：永远不成立
                // 条件二：永远不成立
                // 条件三：永远不成立
                // 条件四：在新扩容表中重新路由定位 hash 对应的头结点
                //        true ->  1.在oldTable中对应的桶位在迁移之前就是null
                //        false -> 2.扩容完成后，有其它写线程，将此桶位设置为了null
                if (k == null
                        || tab == null
                        || (n = tab.length) == 0
                        || (e = tabAt(tab, (n - 1) & h)) == null) {
                    return null;
                }
                // ---------------------------------------------------------------------------
                // 自旋2
                // 前置条件：扩容后的表对应hash的桶位一定不是null，e为此桶位的头结点
                // e可能为哪些node类型？
                //		1.node 类型
                //		2.TreeBin 类型
                //		3.FWD类型
                for(; ; ) {
                    // eh 新扩容后表指定桶位的当前节点的hash
                    // ek 新扩容后表指定桶位的当前节点的key
                    int eh;
                    K ek;
                    // CASE1条件成立：说明新扩容后的表，当前命中桶位中的数据，即为查询想要数据。
                    if ((eh = e.hash) == h
                            && ((ek = e.key) == k || (ek != null && k.equals(ek)))) {
                        return e;
                    }
                    // CASE2: eh < 0 时
                    // 1.TreeBin 类型
                    // 2.FWD类型（新扩容的表，在并发很大的情况下，可能在此方法再次拿到FWD类型），即可能又发生了扩容
                    if (eh < 0) {
                        // 判断是否是FWD结点
                        if (e instanceof ForwardingNode) {
                            // 是FWD结点
                            tab = ((ForwardingNode<K, V>) e).nextTable;
                            // 跳转到自旋1
                            continue outer;
                        }
                        // 不是FWD结点
                        // 说明此桶位 为 TreeBin 节点，使用TreeBin.find 查找红黑树中相应节点。
                        else {
                            return e.find(h, k);
                        }
                    }
                    // 前置条件：当前桶位头结点 并没有命中查询，说明此桶位是链表
                    // 1.将当前元素指向链表的下一个元素
                    // 2.判断当前元素的下一个位置是否为空
                    //   	true -> 说明迭代到链表末尾，未找到对应的数据，返回Null
                    if ((e = e.next) == null) {
                        return null;
                    }
                }
            }
        }
    }
    
    /**
     * A place-holder node used in computeIfAbsent and compute.
     */
    // 占位结点解决 computeIfAbsent bug
    static final class ReservationNode<K, V> extends Node<K, V> {
        ReservationNode() {
            super(RESERVED, null, null);
        }
        
        Node<K, V> find(int h, Object k) {
            return null;
        }
    }
    
    
    
    /**
     * Base class for views.
     */
    abstract static class CollectionView<K, V, E> implements Collection<E>, Serializable {
        private static final long serialVersionUID = 7249069246763182397L;
        
        final ConcurrentHashMap<K, V> map;
        
        private static final String OOME_MSG = "Required array size too large";
        
        CollectionView(ConcurrentHashMap<K, V> map) {
            this.map = map;
        }
        
        /**
         * Returns an iterator over the elements in this collection.
         *
         * <p>The returned iterator is
         * <a href="package-summary.html#Weakly"><i>weakly consistent</i></a>.
         *
         * @return an iterator over the elements in this collection
         */
        public abstract Iterator<E> iterator();
        
        public abstract boolean contains(Object o);
        
        public abstract boolean remove(Object o);
        
        // implementations below rely on concrete classes supplying these abstract methods
        
        /**
         * Removes all of the elements from this view, by removing all
         * the mappings from the map backing this view.
         */
        public final void clear() {
            map.clear();
        }
        
        public final int size() {
            return map.size();
        }
        
        public final boolean isEmpty() {
            return map.isEmpty();
        }
        
        public final Object[] toArray() {
            long sz = map.mappingCount();
            if(sz>MAX_ARRAY_SIZE)
                throw new OutOfMemoryError(OOME_MSG);
            int n = (int) sz;
            Object[] r = new Object[n];
            int i = 0;
            for(E e : this) {
                if(i == n) {
                    if(n >= MAX_ARRAY_SIZE)
                        throw new OutOfMemoryError(OOME_MSG);
                    if(n >= MAX_ARRAY_SIZE - (MAX_ARRAY_SIZE >>> 1) - 1)
                        n = MAX_ARRAY_SIZE;
                    else
                        n += (n >>> 1) + 1;
                    r = Arrays.copyOf(r, n);
                }
                r[i++] = e;
            }
            return (i == n) ? r : Arrays.copyOf(r, i);
        }
        
        @SuppressWarnings("unchecked")
        public final <T> T[] toArray(T[] a) {
            long sz = map.mappingCount();
            if(sz>MAX_ARRAY_SIZE)
                throw new OutOfMemoryError(OOME_MSG);
            int m = (int) sz;
            T[] r = (a.length >= m) ? a : (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), m);
            int n = r.length;
            int i = 0;
            for(E e : this) {
                if(i == n) {
                    if(n >= MAX_ARRAY_SIZE)
                        throw new OutOfMemoryError(OOME_MSG);
                    if(n >= MAX_ARRAY_SIZE - (MAX_ARRAY_SIZE >>> 1) - 1)
                        n = MAX_ARRAY_SIZE;
                    else
                        n += (n >>> 1) + 1;
                    r = Arrays.copyOf(r, n);
                }
                r[i++] = (T) e;
            }
            if(a == r && i<n) {
                r[i] = null; // null-terminate
                return r;
            }
            return (i == n) ? r : Arrays.copyOf(r, i);
        }
        
        /**
         * Returns a string representation of this collection.
         * The string representation consists of the string representations
         * of the collection's elements in the order they are returned by
         * its iterator, enclosed in square brackets ({@code "[]"}).
         * Adjacent elements are separated by the characters {@code ", "}
         * (comma and space).  Elements are converted to strings as by
         * {@link String#valueOf(Object)}.
         *
         * @return a string representation of this collection
         */
        public final String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append('[');
            Iterator<E> it = iterator();
            if(it.hasNext()) {
                for(; ; ) {
                    Object e = it.next();
                    sb.append(e == this ? "(this Collection)" : e);
                    if(!it.hasNext())
                        break;
                    sb.append(',').append(' ');
                }
            }
            return sb.append(']').toString();
        }
        
        public final boolean containsAll(Collection<?> c) {
            if(c != this) {
                for(Object e : c) {
                    if(e == null || !contains(e))
                        return false;
                }
            }
            return true;
        }
        
        public final boolean retainAll(Collection<?> c) {
            if(c == null)
                throw new NullPointerException();
            boolean modified = false;
            for(Iterator<E> it = iterator(); it.hasNext(); ) {
                if(!c.contains(it.next())) {
                    it.remove();
                    modified = true;
                }
            }
            return modified;
        }
        
        /**
         * Returns the map backing this view.
         *
         * @return the map backing this view
         */
        public ConcurrentHashMap<K, V> getMap() {
            return map;
        }
        
        public boolean removeAll(Collection<?> c) {
            if(c == null)
                throw new NullPointerException();
            boolean modified = false;
            // Use (c instanceof Set) as a hint that lookup in c is as
            // efficient as this view
            Node<K, V>[] t;
            if((t = map.table) == null) {
                return false;
            } else if(c instanceof Set<?> && c.size()>t.length) {
                for(Iterator<?> it = iterator(); it.hasNext(); ) {
                    if(c.contains(it.next())) {
                        it.remove();
                        modified = true;
                    }
                }
            } else {
                for(Object e : c)
                    modified |= remove(e);
            }
            return modified;
        }
        
    }
    
    /**
     * A view of a ConcurrentHashMap as a {@link Set} of keys, in
     * which additions may optionally be enabled by mapping to a
     * common value.  This class cannot be directly instantiated.
     * See {@link #keySet() keySet()},
     * {@link #keySet(Object) keySet(V)},
     * {@link #newKeySet() newKeySet()},
     * {@link #newKeySet(int) newKeySet(int)}.
     *
     * @since 1.8
     */
    public static class KeySetView<K,V> extends CollectionView<K,V,K> implements Set<K>, Serializable {
        
        private static final long serialVersionUID = 7249069246763182397L;
        
        private final V value;
        
        KeySetView(ConcurrentHashMap<K, V> map, V value) {  // non-public
            super(map);
            this.value = value;
        }
        
        /**
         * Returns the default mapped value for additions,
         * or {@code null} if additions are not supported.
         *
         * @return the default mapped value for additions, or {@code null}
         * if not supported
         */
        public V getMappedValue() {
            return value;
        }
        
        /**
         * {@inheritDoc}
         *
         * @throws NullPointerException if the specified key is null
         */
        public boolean contains(Object o) {
            return map.containsKey(o);
        }
        
        /**
         * Removes the key from this map view, by removing the key (and its
         * corresponding value) from the backing map.  This method does
         * nothing if the key is not in the map.
         *
         * @param o the key to be removed from the backing map
         *
         * @return {@code true} if the backing map contained the specified key
         *
         * @throws NullPointerException if the specified key is null
         */
        public boolean remove(Object o) {
            return map.remove(o) != null;
        }
        
        /**
         * @return an iterator over the keys of the backing map
         */
        public Iterator<K> iterator() {
            Node<K, V>[] t;
            ConcurrentHashMap<K, V> m = map;
            int f = (t = m.table) == null ? 0 : t.length;
            return new KeyIterator<K, V>(t, f, 0, f, m);
        }
        
        /**
         * Adds the specified key to this set view by mapping the key to
         * the default mapped value in the backing map, if defined.
         *
         * @param e key to be added
         *
         * @return {@code true} if this set changed as a result of the call
         *
         * @throws NullPointerException          if the specified key is null
         * @throws UnsupportedOperationException if no default mapped value
         *                                       for additions was provided
         */
        public boolean add(K e) {
            V v = value;
            if(v == null) {
                throw new UnsupportedOperationException();
            }
            
            return map.putVal(e, v, true) == null;
        }
        
        /**
         * Adds all of the elements in the specified collection to this set,
         * as if by calling {@link #add} on each one.
         *
         * @param c the elements to be inserted into this set
         *
         * @return {@code true} if this set changed as a result of the call
         *
         * @throws NullPointerException          if the collection or any of its
         *                                       elements are {@code null}
         * @throws UnsupportedOperationException if no default mapped value
         *                                       for additions was provided
         */
        public boolean addAll(Collection<? extends K> c) {
            boolean added = false;
            V v = value;
            
            if(v == null) {
                throw new UnsupportedOperationException();
            }
            
            for(K e : c) {
                if(map.putVal(e, v, true) == null) {
                    added = true;
                }
            }
            
            return added;
        }
        
        public int hashCode() {
            int h = 0;
            for(K e : this) {
                h += e.hashCode();
            }
            return h;
        }
        
        public boolean equals(Object o) {
            Set<?> c;
            return (o instanceof Set) && ((c = (Set<?>) o) == this || (containsAll(c) && c.containsAll(this)));
        }
        
        public Spliterator<K> spliterator() {
            Node<K, V>[] t;
            ConcurrentHashMap<K, V> m = map;
            long n = m.sumCount();
            int f = (t = m.table) == null ? 0 : t.length;
            return new KeySpliterator<K, V>(t, f, 0, f, n<0L ? 0L : n);
        }
        
        public void forEach(Consumer<? super K> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            Node<K, V>[] t;
            if((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
                for(Node<K, V> p; (p = it.advance()) != null; ) {
                    action.accept(p.key);
                }
            }
        }
    }
    
    /**
     * A view of a ConcurrentHashMap as a {@link Collection} of
     * values, in which additions are disabled. This class cannot be
     * directly instantiated. See {@link #values()}.
     */
    static final class ValuesView<K,V> extends CollectionView<K,V,V> implements Collection<V>, Serializable {
        
        private static final long serialVersionUID = 2249069246763182397L;
        
        ValuesView(ConcurrentHashMap<K, V> map) {
            super(map);
        }
        
        public final boolean contains(Object o) {
            return map.containsValue(o);
        }
        
        public final boolean remove(Object o) {
            if(o != null) {
                for(Iterator<V> it = iterator(); it.hasNext(); ) {
                    if(o.equals(it.next())) {
                        it.remove();
                        return true;
                    }
                }
            }
            return false;
        }
        
        public final Iterator<V> iterator() {
            ConcurrentHashMap<K, V> m = map;
            Node<K, V>[] t;
            int f = (t = m.table) == null ? 0 : t.length;
            return new ValueIterator<K, V>(t, f, 0, f, m);
        }
        
        public final boolean add(V e) {
            throw new UnsupportedOperationException();
        }
        
        public final boolean addAll(Collection<? extends V> c) {
            throw new UnsupportedOperationException();
        }
        
        @Override
        public boolean removeAll(Collection<?> c) {
            if(c == null) {
                throw new NullPointerException();
            }
            
            boolean modified = false;
            for(Iterator<V> it = iterator(); it.hasNext(); ) {
                if(c.contains(it.next())) {
                    it.remove();
                    modified = true;
                }
            }
            
            return modified;
        }
        
        public boolean removeIf(Predicate<? super V> filter) {
            return map.removeValueIf(filter);
        }
        
        public Spliterator<V> spliterator() {
            Node<K, V>[] t;
            ConcurrentHashMap<K, V> m = map;
            long n = m.sumCount();
            int f = (t = m.table) == null ? 0 : t.length;
            return new ValueSpliterator<K, V>(t, f, 0, f, n<0L ? 0L : n);
        }
        
        public void forEach(Consumer<? super V> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            Node<K, V>[] t;
            if((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
                for(Node<K, V> p; (p = it.advance()) != null; ) {
                    action.accept(p.val);
                }
            }
        }
    }
    
    /**
     * A view of a ConcurrentHashMap as a {@link Set} of (key, value)
     * entries.  This class cannot be directly instantiated. See
     * {@link #entrySet()}.
     */
    static final class EntrySetView<K, V> extends CollectionView<K, V, Map.Entry<K, V>> implements Set<Map.Entry<K, V>>, java.io.Serializable {
        private static final long serialVersionUID = 2249069246763182397L;
        
        EntrySetView(ConcurrentHashMap<K, V> map) {
            super(map);
        }
        
        public final int hashCode() {
            int h = 0;
            Node<K, V>[] t;
            if((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
                for(Node<K, V> p; (p = it.advance()) != null; ) {
                    h += p.hashCode();
                }
            }
            return h;
        }
        
        public final boolean equals(Object o) {
            Set<?> c;
            return ((o instanceof Set) && ((c = (Set<?>) o) == this || (containsAll(c) && c.containsAll(this))));
        }
        
        public boolean contains(Object o) {
            Object k, v, r;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry)
                && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                && (r = map.get(k)) != null
                && (v = e.getValue()) != null
                && (v == r || v.equals(r)));
        }
        
        public boolean remove(Object o) {
            Object k, v;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry)
                && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                && (v = e.getValue()) != null
                && map.remove(k, v));
        }
        
        /**
         * @return an iterator over the entries of the backing map
         */
        public Iterator<Map.Entry<K, V>> iterator() {
            ConcurrentHashMap<K, V> m = map;
            Node<K, V>[] t;
            int f = (t = m.table) == null ? 0 : t.length;
            return new EntryIterator<K, V>(t, f, 0, f, m);
        }
        
        public boolean add(Entry<K, V> e) {
            return map.putVal(e.getKey(), e.getValue(), false) == null;
        }
        
        public boolean addAll(Collection<? extends Entry<K, V>> c) {
            boolean added = false;
            for(Entry<K, V> e : c) {
                if(add(e))
                    added = true;
            }
            return added;
        }
        
        public boolean removeIf(Predicate<? super Entry<K, V>> filter) {
            return map.removeEntryIf(filter);
        }
        
        public Spliterator<Map.Entry<K, V>> spliterator() {
            Node<K, V>[] t;
            ConcurrentHashMap<K, V> m = map;
            long n = m.sumCount();
            int f = (t = m.table) == null ? 0 : t.length;
            return new EntrySpliterator<K, V>(t, f, 0, f, n<0L ? 0L : n, m);
        }
        
        public void forEach(Consumer<? super Map.Entry<K, V>> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            Node<K, V>[] t;
            
            if((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<K, V>(t, t.length, 0, t.length);
                for(Node<K, V> p; (p = it.advance()) != null; ) {
                    action.accept(new MapEntry<K, V>(p.key, p.val, map));
                }
            }
        }
    }
    
    
    
    /**
     * Exported Entry for EntryIterator.
     */
    static final class MapEntry<K, V> implements Map.Entry<K, V> {
        final K key; // non-null
        final ConcurrentHashMap<K, V> map;
        V val;       // non-null
        
        MapEntry(K key, V val, ConcurrentHashMap<K, V> map) {
            this.key = key;
            this.val = val;
            this.map = map;
        }
        
        public K getKey() {
            return key;
        }
        
        public V getValue() {
            return val;
        }
        
        public int hashCode() {
            return key.hashCode() ^ val.hashCode();
        }
        
        public String toString() {
            return Helpers.mapEntryToString(key, val);
        }
        
        public boolean equals(Object o) {
            Object k, v;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null && (v = e.getValue()) != null && (k == key || k.equals(key)) && (v == val || v.equals(val)));
        }
        
        /**
         * Sets our entry's value and writes through to the map. The
         * value to return is somewhat arbitrary here. Since we do not
         * necessarily track asynchronous changes, the most recent
         * "previous" value could be different from what we return (or
         * could even have been removed, in which case the put will
         * re-establish). We do not and cannot guarantee more.
         */
        public V setValue(V value) {
            if(value == null) {
                throw new NullPointerException();
            }
            V v = val;
            val = value;
            map.put(key, value);
            return v;
        }
    }
    
    /**
     * Base of key, value, and entry Iterators. Adds fields to
     * Traverser to support iterator.remove.
     */
    static class BaseIterator<K, V> extends Traverser<K, V> {
        final ConcurrentHashMap<K, V> map;
        Node<K, V> lastReturned;
        
        BaseIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit);
            this.map = map;
            advance();
        }
        
        public final boolean hasNext() {
            return next != null;
        }
        
        public final boolean hasMoreElements() {
            return next != null;
        }
        
        public final void remove() {
            Node<K, V> p;
            if((p = lastReturned) == null) {
                throw new IllegalStateException();
            }
            lastReturned = null;
            map.replaceNode(p.key, null, null);
        }
    }
    
    static final class KeyIterator<K, V> extends BaseIterator<K, V> implements Iterator<K>, Enumeration<K> {
        KeyIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }
        
        public final K next() {
            Node<K, V> p;
            if((p = next) == null) {
                throw new NoSuchElementException();
            }
            K k = p.key;
            lastReturned = p;
            advance();
            return k;
        }
        
        public final K nextElement() {
            return next();
        }
    }
    
    static final class ValueIterator<K, V> extends BaseIterator<K, V> implements Iterator<V>, Enumeration<V> {
        ValueIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }
        
        public final V next() {
            Node<K, V> p;
            if((p = next) == null) {
                throw new NoSuchElementException();
            }
            V v = p.val;
            lastReturned = p;
            advance();
            return v;
        }
        
        public final V nextElement() {
            return next();
        }
    }
    
    static final class EntryIterator<K, V> extends BaseIterator<K, V> implements Iterator<Map.Entry<K, V>> {
        EntryIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }
        
        public final Map.Entry<K, V> next() {
            Node<K, V> p;
            if((p = next) == null) {
                throw new NoSuchElementException();
            }
            K k = p.key;
            V v = p.val;
            lastReturned = p;
            advance();
            return new MapEntry<K, V>(k, v, map);
        }
    }
    
    
    
    /**
     * Records the table, its length, and current traversal index for a
     * traverser that must process a region of a forwarded table before
     * proceeding with current table.
     */
    static final class TableStack<K, V> {
        int length;
        int index;
        Node<K, V>[] tab;
        TableStack<K, V> next;
    }
    
    /**
     * Encapsulates traversal for methods such as containsValue; also
     * serves as a base class for other iterators and spliterators.
     *
     * Method advance visits once each still-valid node that was
     * reachable upon iterator construction. It might miss some that
     * were added to a bin after the bin was visited, which is OK wrt
     * consistency guarantees. Maintaining this property in the face
     * of possible ongoing resizes requires a fair amount of
     * bookkeeping state that is difficult to optimize away amidst
     * volatile accesses.  Even so, traversal maintains reasonable
     * throughput.
     *
     * Normally, iteration proceeds bin-by-bin traversing lists.
     * However, if the table has been resized, then all future steps
     * must traverse both the bin at the current index as well as at
     * (index + baseSize); and so on for further resizings. To
     * paranoically cope with potential sharing by users of iterators
     * across threads, iteration terminates if a bounds checks fails
     * for a table read.
     */
    static class Traverser<K, V> {
        final int baseSize;     // initial table size
        Node<K, V>[] tab;        // current table; updated if resized
        Node<K, V> next;         // the next entry to use
        TableStack<K, V> stack, spare; // to save/restore on ForwardingNodes
        int index;              // index of bin to use next
        int baseIndex;          // current index of initial table
        int baseLimit;          // index bound for initial table
        
        Traverser(Node<K, V>[] tab, int size, int index, int limit) {
            this.tab = tab;
            this.baseSize = size;
            this.baseIndex = this.index = index;
            this.baseLimit = limit;
            this.next = null;
        }
        
        /**
         * Advances if possible, returning next valid node, or null if none.
         */
        final Node<K, V> advance() {
            Node<K, V> e;
            
            if((e = next) != null) {
                e = e.next;
            }
            
            for(; ; ) {
                Node<K, V>[] t;
                int i, n;  // must use locals in checks
                
                if(e != null) {
                    return next = e;
                }
                
                if(baseIndex >= baseLimit || (t = tab) == null || (n = t.length)<=(i = index) || i<0) {
                    return next = null;
                }
                
                if((e = tabAt(t, i)) != null && e.hash<0) {
                    if(e instanceof ForwardingNode) {
                        tab = ((ForwardingNode<K, V>) e).nextTable;
                        e = null;
                        pushState(t, i, n);
                        continue;
                    } else if(e instanceof TreeBin) {
                        e = ((TreeBin<K, V>) e).first;
                    } else {
                        e = null;
                    }
                }
                
                if(stack != null) {
                    recoverState(n);
                } else if((index = i + baseSize) >= n) {
                    index = ++baseIndex; // visit upper slots if present
                }
            }
        }
        
        /**
         * Saves traversal state upon encountering a forwarding node.
         */
        private void pushState(Node<K, V>[] t, int i, int n) {
            TableStack<K, V> s = spare;  // reuse if possible
            if(s != null) {
                spare = s.next;
            } else {
                s = new TableStack<K, V>();
            }
            s.tab = t;
            s.length = n;
            s.index = i;
            s.next = stack;
            stack = s;
        }
        
        /**
         * Possibly pops traversal state.
         *
         * @param n length of current table
         */
        private void recoverState(int n) {
            TableStack<K, V> s;
            int len;
            
            while((s = stack) != null && (index += (len = s.length)) >= n) {
                n = len;
                index = s.index;
                tab = s.tab;
                s.tab = null;
                TableStack<K, V> next = s.next;
                s.next = spare; // save for reuse
                stack = next;
                spare = s;
            }
            
            if(s == null && (index += baseSize) >= n) {
                index = ++baseIndex;
            }
        }
    }
    
    static final class KeySpliterator<K, V> extends Traverser<K, V> implements Spliterator<K> {
        long est;               // size estimate
        
        KeySpliterator(Node<K, V>[] tab, int size, int index, int limit, long est) {
            super(tab, size, index, limit);
            this.est = est;
        }
        
        public KeySpliterator<K, V> trySplit() {
            int i, f, h;
            return (h = ((i = baseIndex) + (f = baseLimit)) >>> 1)<=i ? null : new KeySpliterator<K, V>(tab, baseSize, baseLimit = h, f, est >>>= 1);
        }
        
        public void forEachRemaining(Consumer<? super K> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            for(Node<K, V> p; (p = advance()) != null; ) {
                action.accept(p.key);
            }
        }
        
        public boolean tryAdvance(Consumer<? super K> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            Node<K, V> p;
            if((p = advance()) == null) {
                return false;
            }
            
            action.accept(p.key);
            
            return true;
        }
        
        public long estimateSize() {
            return est;
        }
        
        public int characteristics() {
            return Spliterator.DISTINCT | Spliterator.CONCURRENT | Spliterator.NONNULL;
        }
    }
    
    static final class ValueSpliterator<K, V> extends Traverser<K, V> implements Spliterator<V> {
        long est;               // size estimate
        
        ValueSpliterator(Node<K, V>[] tab, int size, int index, int limit, long est) {
            super(tab, size, index, limit);
            this.est = est;
        }
        
        public ValueSpliterator<K, V> trySplit() {
            int i, f, h;
            return (h = ((i = baseIndex) + (f = baseLimit)) >>> 1)<=i ? null : new ValueSpliterator<K, V>(tab, baseSize, baseLimit = h, f, est >>>= 1);
        }
        
        public void forEachRemaining(Consumer<? super V> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            for(Node<K, V> p; (p = advance()) != null; ) {
                action.accept(p.val);
            }
        }
        
        public boolean tryAdvance(Consumer<? super V> action) {
            if(action == null) {
                throw new NullPointerException();
            }
            
            Node<K, V> p;
            if((p = advance()) == null) {
                return false;
            }
            
            action.accept(p.val);
            
            return true;
        }
        
        public long estimateSize() {
            return est;
        }
        
        public int characteristics() {
            return Spliterator.CONCURRENT | Spliterator.NONNULL;
        }
    }
    
    static final class EntrySpliterator<K, V> extends Traverser<K, V> implements Spliterator<Map.Entry<K, V>> {
        final ConcurrentHashMap<K, V> map; // To export MapEntry
        long est;               // size estimate
        
        EntrySpliterator(Node<K, V>[] tab, int size, int index, int limit, long est, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit);
            this.map = map;
            this.est = est;
        }
        
        public EntrySpliterator<K, V> trySplit() {
            int i, f, h;
            return (h = ((i = baseIndex) + (f = baseLimit)) >>> 1)<=i ? null : new EntrySpliterator<K, V>(tab, baseSize, baseLimit = h, f, est >>>= 1, map);
        }
        
        public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action) {
            if(action == null)
                throw new NullPointerException();
            for(Node<K, V> p; (p = advance()) != null; )
                action.accept(new MapEntry<K, V>(p.key, p.val, map));
        }
        
        public boolean tryAdvance(Consumer<? super Map.Entry<K, V>> action) {
            if(action == null)
                throw new NullPointerException();
            Node<K, V> p;
            if((p = advance()) == null)
                return false;
            action.accept(new MapEntry<K, V>(p.key, p.val, map));
            return true;
        }
        
        public long estimateSize() {
            return est;
        }
        
        public int characteristics() {
            return Spliterator.DISTINCT | Spliterator.CONCURRENT | Spliterator.NONNULL;
        }
    }
    
    
    
    /**
     * Base class for bulk tasks. Repeats some fields and code from
     * class Traverser, because we need to subclass CountedCompleter.
     */
    @SuppressWarnings("serial")
    abstract static class BulkTask<K,V,R> extends CountedCompleter<R> {
        Node<K,V>[] tab;        // same as Traverser
        Node<K,V> next;
        TableStack<K,V> stack, spare;
        int index;
        int baseIndex;
        int baseLimit;
        final int baseSize;
        int batch;              // split control
        
        BulkTask(BulkTask<K,V,?> par, int b, int i, int f, Node<K,V>[] t) {
            super(par);
            this.batch = b;
            this.index = this.baseIndex = i;
            if ((this.tab = t) == null) {
                this.baseSize = this.baseLimit = 0;
            } else if (par == null) {
                this.baseSize = this.baseLimit = t.length;
            } else {
                this.baseLimit = f;
                this.baseSize = par.baseSize;
            }
        }
        
        /**
         * Same as Traverser version.
         */
        final Node<K,V> advance() {
            Node<K,V> e;
            
            if ((e = next) != null) {
                e = e.next;
            }
            
            for (;;) {
                Node<K,V>[] t; int i, n;
                if (e != null) {
                    return next = e;
                }
                
                if (baseIndex >= baseLimit || (t = tab) == null ||
                    (n = t.length) <= (i = index) || i < 0) {
                    return next = null;
                }
                
                if ((e = tabAt(t, i)) != null && e.hash < 0) {
                    if (e instanceof ForwardingNode) {
                        tab = ((ForwardingNode<K,V>)e).nextTable;
                        e = null;
                        pushState(t, i, n);
                        continue;
                    } else if (e instanceof TreeBin) {
                        e = ((TreeBin<K,V>)e).first;
                    } else {
                        e = null;
                    }
                }
                
                if (stack != null) {
                    recoverState(n);
                } else if ((index = i + baseSize) >= n) {
                    index = ++baseIndex;
                }
            }
        }
        
        private void pushState(Node<K,V>[] t, int i, int n) {
            TableStack<K,V> s = spare;
            if (s != null) {
                spare = s.next;
            } else {
                s = new TableStack<K,V>();
            }
            s.tab = t;
            s.length = n;
            s.index = i;
            s.next = stack;
            stack = s;
        }
        
        private void recoverState(int n) {
            TableStack<K,V> s; int len;
            while ((s = stack) != null && (index += (len = s.length)) >= n) {
                n = len;
                index = s.index;
                tab = s.tab;
                s.tab = null;
                TableStack<K,V> next = s.next;
                s.next = spare; // save for reuse
                stack = next;
                spare = s;
            }
            
            if (s == null && (index += baseSize) >= n) {
                index = ++baseIndex;
            }
        }
    }
    
    
    
    /*
     * Task classes. Coded in a regular but ugly format/style to
     * simplify checks that each variant differs in the right way from
     * others. The null screenings exist because compilers cannot tell
     * that we've already null-checked task arguments, so we force
     * simplest hoisted bypass to help avoid convoluted traps.
     */
    @SuppressWarnings("serial")
    static final class ForEachKeyTask<K, V>     extends BulkTask<K, V, Void> {
        final Consumer<? super K> action;
        
        ForEachKeyTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Consumer<? super K> action) {
            super(p, b, i, f, t);
            this.action = action;
        }
        
        public final void compute() {
            final Consumer<? super K> action;
            
            if((action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachKeyTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    action.accept(p.key);
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachValueTask<K, V>   extends BulkTask<K, V, Void> {
        final Consumer<? super V> action;
        
        ForEachValueTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Consumer<? super V> action) {
            super(p, b, i, f, t);
            this.action = action;
        }
        
        public final void compute() {
            final Consumer<? super V> action;
            
            if((action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachValueTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    action.accept(p.val);
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachEntryTask<K, V>   extends BulkTask<K, V, Void> {
        final Consumer<? super Entry<K, V>> action;
        
        ForEachEntryTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Consumer<? super Entry<K, V>> action) {
            super(p, b, i, f, t);
            this.action = action;
        }
        
        public final void compute() {
            final Consumer<? super Entry<K, V>> action;
            
            if((action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachEntryTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    action.accept(p);
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachMappingTask<K, V> extends BulkTask<K, V, Void> {
        final BiConsumer<? super K, ? super V> action;
        
        ForEachMappingTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, BiConsumer<? super K, ? super V> action) {
            super(p, b, i, f, t);
            this.action = action;
        }
        
        public final void compute() {
            final BiConsumer<? super K, ? super V> action;
            
            if((action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachMappingTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    action.accept(p.key, p.val);
                }
                
                propagateCompletion();
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class ForEachTransformedKeyTask<K, V, U>     extends BulkTask<K, V, Void> {
        final Function<? super K, ? extends U> transformer;
        final Consumer<? super U> action;
        
        ForEachTransformedKeyTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<? super K, ? extends U> transformer, Consumer<? super U> action) {
            super(p, b, i, f, t);
            this.transformer = transformer;
            this.action = action;
        }
        
        public final void compute() {
            final Function<? super K, ? extends U> transformer;
            final Consumer<? super U> action;
            
            if((transformer = this.transformer) != null && (action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachTransformedKeyTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, transformer, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u = transformer.apply(p.key);
                    if(u != null) {
                        action.accept(u);
                    }
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachTransformedValueTask<K, V, U>   extends BulkTask<K, V, Void> {
        final Function<? super V, ? extends U> transformer;
        final Consumer<? super U> action;
        
        ForEachTransformedValueTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<? super V, ? extends U> transformer, Consumer<? super U> action) {
            super(p, b, i, f, t);
            this.transformer = transformer;
            this.action = action;
        }
        
        public final void compute() {
            final Function<? super V, ? extends U> transformer;
            final Consumer<? super U> action;
            
            if((transformer = this.transformer) != null && (action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachTransformedValueTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, transformer, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u = transformer.apply(p.val);
                    if(u != null) {
                        action.accept(u);
                    }
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachTransformedEntryTask<K, V, U>   extends BulkTask<K, V, Void> {
        final Function<Map.Entry<K, V>, ? extends U> transformer;
        final Consumer<? super U> action;
        
        ForEachTransformedEntryTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<Map.Entry<K, V>, ? extends U> transformer, Consumer<? super U> action) {
            super(p, b, i, f, t);
            this.transformer = transformer;
            this.action = action;
        }
        
        public final void compute() {
            final Function<Map.Entry<K, V>, ? extends U> transformer;
            final Consumer<? super U> action;
            
            if((transformer = this.transformer) != null && (action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachTransformedEntryTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, transformer, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u = transformer.apply(p);
                    if(u != null) {
                        action.accept(u);
                    }
                }
                
                propagateCompletion();
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ForEachTransformedMappingTask<K, V, U> extends BulkTask<K, V, Void> {
        final BiFunction<? super K, ? super V, ? extends U> transformer;
        final Consumer<? super U> action;
        
        ForEachTransformedMappingTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, BiFunction<? super K, ? super V, ? extends U> transformer, Consumer<? super U> action) {
            super(p, b, i, f, t);
            this.transformer = transformer;
            this.action = action;
        }
        
        public final void compute() {
            final BiFunction<? super K, ? super V, ? extends U> transformer;
            final Consumer<? super U> action;
            if((transformer = this.transformer) != null && (action = this.action) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    new ForEachTransformedMappingTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, transformer, action).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u = transformer.apply(p.key, p.val);
                    if(u != null) {
                        action.accept(u);
                    }
                }
                
                propagateCompletion();
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class SearchKeysTask<K, V, U>     extends BulkTask<K, V, U> {
        final Function<? super K, ? extends U> searchFunction;
        final AtomicReference<U> result;
        
        SearchKeysTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<? super K, ? extends U> searchFunction, AtomicReference<U> result) {
            super(p, b, i, f, t);
            this.searchFunction = searchFunction;
            this.result = result;
        }
        
        public final U getRawResult() {
            return result.get();
        }
        
        public final void compute() {
            final Function<? super K, ? extends U> searchFunction;
            final AtomicReference<U> result;
            
            if((searchFunction = this.searchFunction) != null && (result = this.result) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    if(result.get() != null) {
                        return;
                    }
                    addToPendingCount(1);
                    new SearchKeysTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, searchFunction, result).fork();
                }
                
                while(result.get() == null) {
                    U u;
                    Node<K, V> p;
                    
                    if((p = advance()) == null) {
                        propagateCompletion();
                        break;
                    }
                    
                    if((u = searchFunction.apply(p.key)) != null) {
                        if(result.compareAndSet(null, u)) {
                            quietlyCompleteRoot();
                        }
                        break;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class SearchValuesTask<K, V, U>   extends BulkTask<K, V, U> {
        final Function<? super V, ? extends U> searchFunction;
        final AtomicReference<U> result;
        
        SearchValuesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<? super V, ? extends U> searchFunction, AtomicReference<U> result) {
            super(p, b, i, f, t);
            this.searchFunction = searchFunction;
            this.result = result;
        }
        
        public final U getRawResult() {
            return result.get();
        }
        
        public final void compute() {
            final Function<? super V, ? extends U> searchFunction;
            final AtomicReference<U> result;
            
            if((searchFunction = this.searchFunction) != null && (result = this.result) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    if(result.get() != null) {
                        return;
                    }
                    addToPendingCount(1);
                    new SearchValuesTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, searchFunction, result).fork();
                }
                
                while(result.get() == null) {
                    U u;
                    Node<K, V> p;
                    
                    if((p = advance()) == null) {
                        propagateCompletion();
                        break;
                    }
                    
                    if((u = searchFunction.apply(p.val)) != null) {
                        if(result.compareAndSet(null, u)) {
                            quietlyCompleteRoot();
                        }
                        break;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class SearchEntriesTask<K, V, U>  extends BulkTask<K, V, U> {
        final Function<Entry<K, V>, ? extends U> searchFunction;
        final AtomicReference<U> result;
        
        SearchEntriesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, Function<Entry<K, V>, ? extends U> searchFunction, AtomicReference<U> result) {
            super(p, b, i, f, t);
            this.searchFunction = searchFunction;
            this.result = result;
        }
        
        public final U getRawResult() {
            return result.get();
        }
        
        public final void compute() {
            final Function<Entry<K, V>, ? extends U> searchFunction;
            final AtomicReference<U> result;
            
            if((searchFunction = this.searchFunction) != null && (result = this.result) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    if(result.get() != null) {
                        return;
                    }
                    addToPendingCount(1);
                    new SearchEntriesTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, searchFunction, result).fork();
                }
                
                while(result.get() == null) {
                    U u;
                    Node<K, V> p;
                    
                    if((p = advance()) == null) {
                        propagateCompletion();
                        break;
                    }
                    
                    if((u = searchFunction.apply(p)) != null) {
                        if(result.compareAndSet(null, u)) {
                            quietlyCompleteRoot();
                        }
                        return;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class SearchMappingsTask<K, V, U> extends BulkTask<K, V, U> {
        final BiFunction<? super K, ? super V, ? extends U> searchFunction;
        final AtomicReference<U> result;
        
        SearchMappingsTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, BiFunction<? super K, ? super V, ? extends U> searchFunction, AtomicReference<U> result) {
            super(p, b, i, f, t);
            this.searchFunction = searchFunction;
            this.result = result;
        }
        
        public final U getRawResult() {
            return result.get();
        }
        
        public final void compute() {
            final BiFunction<? super K, ? super V, ? extends U> searchFunction;
            final AtomicReference<U> result;
            
            if((searchFunction = this.searchFunction) != null && (result = this.result) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    if(result.get() != null) {
                        return;
                    }
                    addToPendingCount(1);
                    new SearchMappingsTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, searchFunction, result).fork();
                }
                
                while(result.get() == null) {
                    U u;
                    Node<K, V> p;
                    
                    if((p = advance()) == null) {
                        propagateCompletion();
                        break;
                    }
                    
                    if((u = searchFunction.apply(p.key, p.val)) != null) {
                        if(result.compareAndSet(null, u)) {
                            quietlyCompleteRoot();
                        }
                        break;
                    }
                }
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class ReduceKeysTask<K, V>    extends BulkTask<K, V, K> {
        final BiFunction<? super K, ? super K, ? extends K> reducer;
        K result;
        ReduceKeysTask<K, V> rights, nextRight;
        
        ReduceKeysTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, ReduceKeysTask<K, V> nextRight, BiFunction<? super K, ? super K, ? extends K> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.reducer = reducer;
        }
        
        public final K getRawResult() {
            return result;
        }
        
        public final void compute() {
            final BiFunction<? super K, ? super K, ? extends K> reducer;
            if((reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new ReduceKeysTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, reducer)).fork();
                }
                
                K r = null;
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    K u = p.key;
                    r = (r == null) ? u : u == null ? r : reducer.apply(r, u);
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    ReduceKeysTask<K, V> t = (ReduceKeysTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        K tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ReduceValuesTask<K, V>  extends BulkTask<K, V, V> {
        final BiFunction<? super V, ? super V, ? extends V> reducer;
        V result;
        ReduceValuesTask<K, V> rights, nextRight;
        
        ReduceValuesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, ReduceValuesTask<K, V> nextRight, BiFunction<? super V, ? super V, ? extends V> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.reducer = reducer;
        }
        
        public final V getRawResult() {
            return result;
        }
        
        public final void compute() {
            final BiFunction<? super V, ? super V, ? extends V> reducer;
            if((reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new ReduceValuesTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, reducer)).fork();
                }
                
                V r = null;
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    V v = p.val;
                    r = (r == null) ? v : reducer.apply(r, v);
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    ReduceValuesTask<K, V> t = (ReduceValuesTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        V tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class ReduceEntriesTask<K, V> extends BulkTask<K, V, Map.Entry<K, V>> {
        final BiFunction<Map.Entry<K, V>, Map.Entry<K, V>, ? extends Map.Entry<K, V>> reducer;
        Map.Entry<K, V> result;
        ReduceEntriesTask<K, V> rights, nextRight;
        
        ReduceEntriesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, ReduceEntriesTask<K, V> nextRight, BiFunction<Entry<K, V>, Map.Entry<K, V>, ? extends Map.Entry<K, V>> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.reducer = reducer;
        }
        
        public final Map.Entry<K, V> getRawResult() {
            return result;
        }
        
        public final void compute() {
            final BiFunction<Map.Entry<K, V>, Map.Entry<K, V>, ? extends Map.Entry<K, V>> reducer;
            if((reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new ReduceEntriesTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, reducer)).fork();
                }
                
                Map.Entry<K, V> r = null;
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = (r == null) ? p : reducer.apply(r, p);
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    ReduceEntriesTask<K, V> t = (ReduceEntriesTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        Map.Entry<K, V> tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class MapReduceKeysTask<K, V, U> extends BulkTask<K, V, U> {
        final Function<? super K, ? extends U> transformer;
        final BiFunction<? super U, ? super U, ? extends U> reducer;
        U result;
        MapReduceKeysTask<K, V, U> rights, nextRight;
        
        MapReduceKeysTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceKeysTask<K, V, U> nextRight, Function<? super K, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.reducer = reducer;
        }
        
        public final U getRawResult() {
            return result;
        }
        
        public final void compute() {
            final Function<? super K, ? extends U> transformer;
            final BiFunction<? super U, ? super U, ? extends U> reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceKeysTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, reducer)).fork();
                }
                
                U r = null;
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u;
                    if((u = transformer.apply(p.key)) != null) {
                        r = (r == null) ? u : reducer.apply(r, u);
                    }
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceKeysTask<K, V, U> t = (MapReduceKeysTask<K, V, U>) c, s = t.rights;
                    while(s != null) {
                        U tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceValuesTask<K, V, U> extends BulkTask<K, V, U> {
        final Function<? super V, ? extends U> transformer;
        final BiFunction<? super U, ? super U, ? extends U> reducer;
        U result;
        MapReduceValuesTask<K, V, U> rights, nextRight;
        
        MapReduceValuesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceValuesTask<K, V, U> nextRight, Function<? super V, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.reducer = reducer;
        }
        
        public final U getRawResult() {
            return result;
        }
        
        public final void compute() {
            final Function<? super V, ? extends U> transformer;
            final BiFunction<? super U, ? super U, ? extends U> reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceValuesTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, reducer)).fork();
                }
                
                U r = null;
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u;
                    if((u = transformer.apply(p.val)) != null) {
                        r = (r == null) ? u : reducer.apply(r, u);
                    }
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceValuesTask<K, V, U> t = (MapReduceValuesTask<K, V, U>) c, s = t.rights;
                    while(s != null) {
                        U tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceEntriesTask<K, V, U> extends BulkTask<K, V, U> {
        final Function<Map.Entry<K, V>, ? extends U> transformer;
        final BiFunction<? super U, ? super U, ? extends U> reducer;
        U result;
        MapReduceEntriesTask<K, V, U> rights, nextRight;
        
        MapReduceEntriesTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceEntriesTask<K, V, U> nextRight, Function<Map.Entry<K, V>, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.reducer = reducer;
        }
        
        public final U getRawResult() {
            return result;
        }
        
        public final void compute() {
            final Function<Map.Entry<K, V>, ? extends U> transformer;
            final BiFunction<? super U, ? super U, ? extends U> reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceEntriesTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, reducer)).fork();
                }
                
                U r = null;
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u;
                    if((u = transformer.apply(p)) != null)
                        r = (r == null) ? u : reducer.apply(r, u);
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceEntriesTask<K, V, U> t = (MapReduceEntriesTask<K, V, U>) c, s = t.rights;
                    while(s != null) {
                        U tr, sr;
                        if((sr = s.result) != null)
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceMappingsTask<K, V, U> extends BulkTask<K, V, U> {
        final BiFunction<? super K, ? super V, ? extends U> transformer;
        final BiFunction<? super U, ? super U, ? extends U> reducer;
        U result;
        MapReduceMappingsTask<K, V, U> rights, nextRight;
        
        MapReduceMappingsTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceMappingsTask<K, V, U> nextRight, BiFunction<? super K, ? super V, ? extends U> transformer, BiFunction<? super U, ? super U, ? extends U> reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.reducer = reducer;
        }
        
        public final U getRawResult() {
            return result;
        }
        
        public final void compute() {
            final BiFunction<? super K, ? super V, ? extends U> transformer;
            final BiFunction<? super U, ? super U, ? extends U> reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceMappingsTask<K, V, U>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, reducer)).fork();
                }
                
                U r = null;
                for(Node<K, V> p; (p = advance()) != null; ) {
                    U u;
                    if((u = transformer.apply(p.key, p.val)) != null) {
                        r = (r == null) ? u : reducer.apply(r, u);
                    }
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceMappingsTask<K, V, U> t = (MapReduceMappingsTask<K, V, U>) c, s = t.rights;
                    while(s != null) {
                        U tr, sr;
                        if((sr = s.result) != null) {
                            t.result = (((tr = t.result) == null) ? sr : reducer.apply(tr, sr));
                        }
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class MapReduceKeysToIntTask<K, V>     extends BulkTask<K, V, Integer> {
        final ToIntFunction<? super K> transformer;
        final IntBinaryOperator reducer;
        final int basis;
        int result;
        MapReduceKeysToIntTask<K, V> rights, nextRight;
        
        MapReduceKeysToIntTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceKeysToIntTask<K, V> nextRight, ToIntFunction<? super K> transformer, int basis, IntBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Integer getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToIntFunction<? super K> transformer;
            final IntBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                int r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceKeysToIntTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsInt(r, transformer.applyAsInt(p.key));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceKeysToIntTask<K, V> t = (MapReduceKeysToIntTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsInt(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceValuesToIntTask<K, V>   extends BulkTask<K, V, Integer> {
        final ToIntFunction<? super V> transformer;
        final IntBinaryOperator reducer;
        final int basis;
        int result;
        MapReduceValuesToIntTask<K, V> rights, nextRight;
        
        MapReduceValuesToIntTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceValuesToIntTask<K, V> nextRight, ToIntFunction<? super V> transformer, int basis, IntBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Integer getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToIntFunction<? super V> transformer;
            final IntBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                int r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceValuesToIntTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsInt(r, transformer.applyAsInt(p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceValuesToIntTask<K, V> t = (MapReduceValuesToIntTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsInt(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceEntriesToIntTask<K, V>  extends BulkTask<K, V, Integer> {
        final ToIntFunction<Map.Entry<K, V>> transformer;
        final IntBinaryOperator reducer;
        final int basis;
        int result;
        MapReduceEntriesToIntTask<K, V> rights, nextRight;
        
        MapReduceEntriesToIntTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceEntriesToIntTask<K, V> nextRight, ToIntFunction<Map.Entry<K, V>> transformer, int basis, IntBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Integer getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToIntFunction<Map.Entry<K, V>> transformer;
            final IntBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                int r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceEntriesToIntTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsInt(r, transformer.applyAsInt(p));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceEntriesToIntTask<K, V> t = (MapReduceEntriesToIntTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsInt(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceMappingsToIntTask<K, V> extends BulkTask<K, V, Integer> {
        final ToIntBiFunction<? super K, ? super V> transformer;
        final IntBinaryOperator reducer;
        final int basis;
        int result;
        MapReduceMappingsToIntTask<K, V> rights, nextRight;
        
        MapReduceMappingsToIntTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceMappingsToIntTask<K, V> nextRight, ToIntBiFunction<? super K, ? super V> transformer, int basis, IntBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Integer getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToIntBiFunction<? super K, ? super V> transformer;
            final IntBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                int r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceMappingsToIntTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsInt(r, transformer.applyAsInt(p.key, p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceMappingsToIntTask<K, V> t = (MapReduceMappingsToIntTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsInt(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class MapReduceKeysToLongTask<K, V>     extends BulkTask<K, V, Long> {
        final ToLongFunction<? super K> transformer;
        final LongBinaryOperator reducer;
        final long basis;
        long result;
        MapReduceKeysToLongTask<K, V> rights, nextRight;
        
        MapReduceKeysToLongTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceKeysToLongTask<K, V> nextRight, ToLongFunction<? super K> transformer, long basis, LongBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Long getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToLongFunction<? super K> transformer;
            final LongBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                long r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceKeysToLongTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsLong(r, transformer.applyAsLong(p.key));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceKeysToLongTask<K, V> t = (MapReduceKeysToLongTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsLong(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceValuesToLongTask<K, V>   extends BulkTask<K, V, Long> {
        final ToLongFunction<? super V> transformer;
        final LongBinaryOperator reducer;
        final long basis;
        long result;
        MapReduceValuesToLongTask<K, V> rights, nextRight;
        
        MapReduceValuesToLongTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceValuesToLongTask<K, V> nextRight, ToLongFunction<? super V> transformer, long basis, LongBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Long getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToLongFunction<? super V> transformer;
            final LongBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                long r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceValuesToLongTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsLong(r, transformer.applyAsLong(p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceValuesToLongTask<K, V> t = (MapReduceValuesToLongTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsLong(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceEntriesToLongTask<K, V>  extends BulkTask<K, V, Long> {
        final ToLongFunction<Map.Entry<K, V>> transformer;
        final LongBinaryOperator reducer;
        final long basis;
        long result;
        MapReduceEntriesToLongTask<K, V> rights, nextRight;
        
        MapReduceEntriesToLongTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceEntriesToLongTask<K, V> nextRight, ToLongFunction<Map.Entry<K, V>> transformer, long basis, LongBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Long getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToLongFunction<Map.Entry<K, V>> transformer;
            final LongBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                long r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceEntriesToLongTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsLong(r, transformer.applyAsLong(p));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceEntriesToLongTask<K, V> t = (MapReduceEntriesToLongTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsLong(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceMappingsToLongTask<K, V> extends BulkTask<K, V, Long> {
        final ToLongBiFunction<? super K, ? super V> transformer;
        final LongBinaryOperator reducer;
        final long basis;
        long result;
        MapReduceMappingsToLongTask<K, V> rights, nextRight;
        
        MapReduceMappingsToLongTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceMappingsToLongTask<K, V> nextRight, ToLongBiFunction<? super K, ? super V> transformer, long basis, LongBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Long getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToLongBiFunction<? super K, ? super V> transformer;
            final LongBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                long r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceMappingsToLongTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsLong(r, transformer.applyAsLong(p.key, p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceMappingsToLongTask<K, V> t = (MapReduceMappingsToLongTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsLong(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    
    
    @SuppressWarnings("serial")
    static final class MapReduceKeysToDoubleTask<K, V>     extends BulkTask<K, V, Double> {
        final ToDoubleFunction<? super K> transformer;
        final DoubleBinaryOperator reducer;
        final double basis;
        double result;
        MapReduceKeysToDoubleTask<K, V> rights, nextRight;
        
        MapReduceKeysToDoubleTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceKeysToDoubleTask<K, V> nextRight, ToDoubleFunction<? super K> transformer, double basis, DoubleBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Double getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToDoubleFunction<? super K> transformer;
            final DoubleBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                double r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceKeysToDoubleTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsDouble(r, transformer.applyAsDouble(p.key));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceKeysToDoubleTask<K, V> t = (MapReduceKeysToDoubleTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsDouble(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceValuesToDoubleTask<K, V>   extends BulkTask<K, V, Double> {
        final ToDoubleFunction<? super V> transformer;
        final DoubleBinaryOperator reducer;
        final double basis;
        double result;
        MapReduceValuesToDoubleTask<K, V> rights, nextRight;
        
        MapReduceValuesToDoubleTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceValuesToDoubleTask<K, V> nextRight, ToDoubleFunction<? super V> transformer, double basis, DoubleBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Double getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToDoubleFunction<? super V> transformer;
            final DoubleBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                double r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceValuesToDoubleTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsDouble(r, transformer.applyAsDouble(p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceValuesToDoubleTask<K, V> t = (MapReduceValuesToDoubleTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsDouble(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceEntriesToDoubleTask<K, V>  extends BulkTask<K, V, Double> {
        final ToDoubleFunction<Map.Entry<K, V>> transformer;
        final DoubleBinaryOperator reducer;
        final double basis;
        double result;
        MapReduceEntriesToDoubleTask<K, V> rights, nextRight;
        
        MapReduceEntriesToDoubleTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceEntriesToDoubleTask<K, V> nextRight, ToDoubleFunction<Map.Entry<K, V>> transformer, double basis, DoubleBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Double getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToDoubleFunction<Map.Entry<K, V>> transformer;
            final DoubleBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                double r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceEntriesToDoubleTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsDouble(r, transformer.applyAsDouble(p));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceEntriesToDoubleTask<K, V> t = (MapReduceEntriesToDoubleTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsDouble(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    @SuppressWarnings("serial")
    static final class MapReduceMappingsToDoubleTask<K, V> extends BulkTask<K, V, Double> {
        final ToDoubleBiFunction<? super K, ? super V> transformer;
        final DoubleBinaryOperator reducer;
        final double basis;
        double result;
        MapReduceMappingsToDoubleTask<K, V> rights, nextRight;
        
        MapReduceMappingsToDoubleTask(BulkTask<K, V, ?> p, int b, int i, int f, Node<K, V>[] t, MapReduceMappingsToDoubleTask<K, V> nextRight, ToDoubleBiFunction<? super K, ? super V> transformer, double basis, DoubleBinaryOperator reducer) {
            super(p, b, i, f, t);
            this.nextRight = nextRight;
            this.transformer = transformer;
            this.basis = basis;
            this.reducer = reducer;
        }
        
        public final Double getRawResult() {
            return result;
        }
        
        public final void compute() {
            final ToDoubleBiFunction<? super K, ? super V> transformer;
            final DoubleBinaryOperator reducer;
            if((transformer = this.transformer) != null && (reducer = this.reducer) != null) {
                double r = this.basis;
                for(int i = baseIndex, f, h; batch>0 && (h = ((f = baseLimit) + i) >>> 1)>i; ) {
                    addToPendingCount(1);
                    (rights = new MapReduceMappingsToDoubleTask<K, V>(this, batch >>>= 1, baseLimit = h, f, tab, rights, transformer, r, reducer)).fork();
                }
                
                for(Node<K, V> p; (p = advance()) != null; ) {
                    r = reducer.applyAsDouble(r, transformer.applyAsDouble(p.key, p.val));
                }
                
                result = r;
                
                for(CountedCompleter<?> c = firstComplete(); c != null; c = c.nextComplete()) {
                    @SuppressWarnings("unchecked")
                    MapReduceMappingsToDoubleTask<K, V> t = (MapReduceMappingsToDoubleTask<K, V>) c, s = t.rights;
                    while(s != null) {
                        t.result = reducer.applyAsDouble(t.result, s.result);
                        s = t.rights = s.nextRight;
                    }
                }
            }
        }
    }
    
    
    
    /**
     * A padded cell for distributing counts.  Adapted from LongAdder
     * and Striped64.  See their internal docs for explanation.
     */
    @jdk.internal.vm.annotation.Contended
    static final class CounterCell {
        volatile long value;
        
        CounterCell(long x) {
            value = x;
        }
    }
    
    
    
    /**
     * Stripped-down version of helper class used in previous version,
     * declared for the sake of serialization compatibility.
     */
    static class Segment<K,V> extends ReentrantLock implements Serializable {
        private static final long serialVersionUID = 2249069246763182397L;
        final float loadFactor;
        Segment(float lf) { this.loadFactor = lf; }
    }
    
}
