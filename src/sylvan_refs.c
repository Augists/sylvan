/*
 * Copyright 2011-2016 Formal Methods and Tools, University of Twente
 * Copyright 2016-2017 Tom van Dijk, Johannes Kepler University Linz
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <sylvan.h>
#include <stdatomic.h>
#include <sylvan_align.h>
#include <sylvan_refs.h>
#include <sylvan_hash.h>

#include <errno.h>  // for errno
#include <string.h> // for strerror
#ifdef SYLVAN_REFS_STATS
#include <inttypes.h>
#include <pthread.h>
#include <time.h>
#endif

#ifndef MTPNDD_LOG_LEVEL
#define MTPNDD_LOG_LEVEL 1
#endif

#ifndef MTPNDD_LOG_LEVEL_DEBUG
#define MTPNDD_LOG_LEVEL_DEBUG 2
#endif

#ifndef compiler_barrier
#define compiler_barrier() atomic_signal_fence(memory_order_seq_cst)
#endif

/**
 * Implementation of external references
 * Based on a hash table for 40-bit non-null values, linear probing
 * Use tombstones for deleting, higher bits for reference count
 */
static const uint64_t refs_ts = 0x7fffffffffffffff; // tombstone

#define fnvhash8(a) sylvan_fnvhash8(a, 14695981039346656037LLU)

static const int32_t refs_count_max = 0x007fffff;
static const int32_t refs_count_min = -0x00800000;

static _Atomic(uint64_t) g_refs_resize_total = 0;
static _Atomic(uint64_t) g_protect_resize_total = 0;

static inline int32_t
refs_unpack_count(uint64_t v)
{
    int32_t count = (int32_t)(v >> 40);
    if (count & 0x00800000) count |= ~0x00ffffff;
    return count;
}

static inline uint64_t
refs_pack_count(uint64_t key, int32_t count)
{
    return (key & 0x000000ffffffffffULL) | ((uint64_t)(count & 0x00ffffff) << 40);
}

#ifdef SYLVAN_REFS_STATS
#define SYLVAN_REFS_STATS_BUCKETS 4096u
#define SYLVAN_REFS_STATS_MAX 8u
#define SYLVAN_REFS_STATS_THREADS 64u
#define SYLVAN_REFS_STATS_TIME_SAMPLE_SHIFT 10u
#define SYLVAN_REFS_STATS_TIME_SAMPLE_MASK ((1u << SYLVAN_REFS_STATS_TIME_SAMPLE_SHIFT) - 1u)

typedef struct refs_stats_entry {
    refs_table_t *tbl;
    const char *name;
    size_t refs_size;
    _Atomic uint64_t modify_calls;
    _Atomic uint64_t ups;
    _Atomic uint64_t downs;
    _Atomic uint64_t updates;
    _Atomic uint64_t misses;
    _Atomic uint64_t probes;
    _Atomic uint64_t retries;
    _Atomic uint64_t time_ns;
    _Atomic uint64_t time_samples;
    _Atomic uint64_t bucket_hist[SYLVAN_REFS_STATS_BUCKETS];
    struct {
        _Atomic int used;
        pthread_t tid;
        uint64_t modify_calls;
        uint64_t ups;
        uint64_t downs;
        uint64_t updates;
        uint64_t misses;
        uint64_t probes;
        uint64_t retries;
        uint64_t time_ns;
        uint64_t time_samples;
    } threads[SYLVAN_REFS_STATS_THREADS];
} refs_stats_entry_t;

static refs_stats_entry_t refs_stats_entries[SYLVAN_REFS_STATS_MAX];
static _Atomic size_t refs_stats_count = 0;
static _Thread_local uint64_t refs_stats_sample_tick = 0;

static inline uint64_t
refs_stats_next_tick(void)
{
    return refs_stats_sample_tick++;
}

static inline uint64_t
refs_stats_timespec_diff_ns(const struct timespec *start, const struct timespec *end)
{
    return (uint64_t)(end->tv_sec - start->tv_sec) * 1000000000ull +
           (uint64_t)(end->tv_nsec - start->tv_nsec);
}

static inline refs_stats_entry_t *
refs_stats_get(refs_table_t *tbl)
{
    return (refs_stats_entry_t *)tbl->stats;
}

static inline void
refs_stats_thread_add(refs_stats_entry_t *entry, int dir, uint64_t probes, uint64_t retries,
                      uint64_t misses, uint64_t updates, uint64_t time_ns, uint64_t time_samples)
{
    if (!entry) return;
    pthread_t tid = pthread_self();
    for (size_t i = 0; i < SYLVAN_REFS_STATS_THREADS; i++) {
        int used = atomic_load_explicit(&entry->threads[i].used, memory_order_relaxed);
        if (used && pthread_equal(entry->threads[i].tid, tid)) {
            entry->threads[i].modify_calls++;
            if (dir > 0) entry->threads[i].ups++;
            else if (dir < 0) entry->threads[i].downs++;
            entry->threads[i].probes += probes;
            entry->threads[i].retries += retries;
            entry->threads[i].misses += misses;
            entry->threads[i].updates += updates;
            entry->threads[i].time_ns += time_ns;
            entry->threads[i].time_samples += time_samples;
            return;
        }
    }
    for (size_t i = 0; i < SYLVAN_REFS_STATS_THREADS; i++) {
        int expected = 0;
        if (atomic_compare_exchange_strong(&entry->threads[i].used, &expected, 1)) {
            entry->threads[i].tid = tid;
            entry->threads[i].modify_calls = 1;
            if (dir > 0) entry->threads[i].ups = 1;
            else if (dir < 0) entry->threads[i].downs = 1;
            entry->threads[i].probes = probes;
            entry->threads[i].retries = retries;
            entry->threads[i].misses = misses;
            entry->threads[i].updates = updates;
            entry->threads[i].time_ns = time_ns;
            entry->threads[i].time_samples = time_samples;
            return;
        }
    }
}

void
refs_stats_register(refs_table_t *tbl, const char *name)
{
    if (!tbl || !name) return;
    size_t idx = atomic_fetch_add(&refs_stats_count, 1);
    if (idx >= SYLVAN_REFS_STATS_MAX) return;
    refs_stats_entry_t *entry = &refs_stats_entries[idx];
    entry->tbl = tbl;
    entry->name = name;
    entry->refs_size = tbl->refs_size;
    tbl->stats = entry;
}

static void
refs_stats_dump_entry(FILE *out, refs_stats_entry_t *entry)
{
    if (!entry || !out) return;
    uint64_t modify_calls = atomic_load_explicit(&entry->modify_calls, memory_order_relaxed);
    uint64_t ups = atomic_load_explicit(&entry->ups, memory_order_relaxed);
    uint64_t downs = atomic_load_explicit(&entry->downs, memory_order_relaxed);
    uint64_t updates = atomic_load_explicit(&entry->updates, memory_order_relaxed);
    uint64_t misses = atomic_load_explicit(&entry->misses, memory_order_relaxed);
    uint64_t probes = atomic_load_explicit(&entry->probes, memory_order_relaxed);
    uint64_t retries = atomic_load_explicit(&entry->retries, memory_order_relaxed);
    uint64_t time_ns = atomic_load_explicit(&entry->time_ns, memory_order_relaxed);
    uint64_t time_samples = atomic_load_explicit(&entry->time_samples, memory_order_relaxed);
    double avg_probes = modify_calls ? ((double)probes / (double)modify_calls) : 0.0;
    double avg_time_ns = time_samples ? ((double)time_ns / (double)time_samples) : 0.0;

    fprintf(out, "[refs-stats] %s\n", entry->name);
    fprintf(out, "[refs-stats] modify_calls=%" PRIu64 " ups=%" PRIu64 " downs=%" PRIu64
                 " updates=%" PRIu64 " misses=%" PRIu64 " retries=%" PRIu64 " avg_probes=%.3f\n",
            modify_calls, ups, downs, updates, misses, retries, avg_probes);
    fprintf(out, "[refs-stats] time_samples=%" PRIu64 " time_ns=%" PRIu64
                 " avg_time_ns=%.1f sample_rate=1/%u\n",
            time_samples, time_ns, avg_time_ns, 1u << SYLVAN_REFS_STATS_TIME_SAMPLE_SHIFT);

    /* Top 8 buckets in histogram (hash into SYLVAN_REFS_STATS_BUCKETS) */
    uint64_t top_counts[8] = {0};
    size_t top_idx[8] = {0};
    for (size_t i = 0; i < SYLVAN_REFS_STATS_BUCKETS; i++) {
        uint64_t v = atomic_load_explicit(&entry->bucket_hist[i], memory_order_relaxed);
        if (v == 0) continue;
        for (size_t j = 0; j < 8; j++) {
            if (v > top_counts[j]) {
                for (size_t k = 7; k > j; k--) {
                    top_counts[k] = top_counts[k-1];
                    top_idx[k] = top_idx[k-1];
                }
                top_counts[j] = v;
                top_idx[j] = i;
                break;
            }
        }
    }
    fprintf(out, "[refs-stats] top_buckets (bucket_mod,count):");
    for (size_t j = 0; j < 8; j++) {
        if (top_counts[j] == 0) break;
        fprintf(out, " %zu=%" PRIu64, top_idx[j], top_counts[j]);
    }
    fprintf(out, "\n");

    for (size_t i = 0; i < SYLVAN_REFS_STATS_THREADS; i++) {
        if (!atomic_load_explicit(&entry->threads[i].used, memory_order_relaxed)) continue;
        fprintf(out, "[refs-stats] thread idx=%zu modify=%" PRIu64 " up=%" PRIu64 " down=%" PRIu64
                     " updates=%" PRIu64 " misses=%" PRIu64 " retries=%" PRIu64 " probes=%" PRIu64
                     " time_ns=%" PRIu64 " time_samples=%" PRIu64 "\n",
                i,
                entry->threads[i].modify_calls,
                entry->threads[i].ups,
                entry->threads[i].downs,
                entry->threads[i].updates,
                entry->threads[i].misses,
                entry->threads[i].retries,
                entry->threads[i].probes,
                entry->threads[i].time_ns,
                entry->threads[i].time_samples);
    }
}

void
refs_stats_dump(FILE *out)
{
    if (!out) out = stderr;
    size_t count = atomic_load_explicit(&refs_stats_count, memory_order_relaxed);
    for (size_t i = 0; i < count; i++) {
        refs_stats_dump_entry(out, &refs_stats_entries[i]);
    }
}
#endif

uint64_t
refs_resize_total(void)
{
    return atomic_load_explicit(&g_refs_resize_total, memory_order_relaxed);
}

uint64_t
protect_resize_total(void)
{
    return atomic_load_explicit(&g_protect_resize_total, memory_order_relaxed);
}

// Count number of unique entries (not number of references)
size_t
refs_count(refs_table_t *tbl)
{
    size_t count = 0;
    _Atomic(uint64_t) *bucket = tbl->refs_table;
    _Atomic(uint64_t) * const end = bucket + tbl->refs_size;
    while (bucket != end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) count++;
        bucket++;
    }
    return count;
}

static inline void
refs_rehash(refs_table_t *tbl, uint64_t v)
{
    if (v == 0) return; // do not rehash empty value
    if (v == refs_ts) return; // do not rehash tombstone

    _Atomic(uint64_t) *bucket = tbl->refs_table + (fnvhash8(v & 0x000000ffffffffff) % tbl->refs_size);
    _Atomic(uint64_t) * const end = tbl->refs_table + tbl->refs_size;

    int i = 128; // try 128 times linear probing
    while (i--) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d == 0) {
            if (atomic_compare_exchange_strong(bucket, &d, v)) return; 
        }
        if (++bucket == end) bucket = (_Atomic(uint64_t) *)tbl->refs_table;
    }

    // assert(0); // impossible!
}

/**
 * Called internally to assist resize operations
 * Returns 1 for retry, 0 for done
 */
static int
refs_resize_help(refs_table_t *tbl)
{
    // TODO optimize??
    if (0 == (tbl->refs_control & 0xf0000000)) return 0; // no resize in progress (anymore)
    if (tbl->refs_control & 0x80000000) return 1; // still waiting for preparation

    if (tbl->refs_resize_part >= tbl->refs_resize_size / 128) return 1; // all parts claimed
    size_t part = atomic_fetch_add(&tbl->refs_resize_part, 1);
    if (part >= tbl->refs_resize_size/128) return 1; // all parts claimed

    // rehash all
    int i;
    _Atomic(uint64_t) *bucket = tbl->refs_resize_table + part * 128;
    for (i=0; i<128; i++) {
        refs_rehash(tbl, atomic_load_explicit(bucket, memory_order_relaxed));
        bucket++;
    }

    atomic_fetch_add(&tbl->refs_resize_done, 1);
    return 1;
}

static void
refs_resize(refs_table_t *tbl)
{
    while (1) {
        uint32_t v = tbl->refs_control;
        if (v & 0xf0000000) {
            // someone else started resize
            // just rehash blocks until done
            while (refs_resize_help(tbl)) continue;
            return;
        }
        if (atomic_compare_exchange_weak(&tbl->refs_control, &v, 0x80000000 | v)) {
#if MTPNDD_LOG_LEVEL >= MTPNDD_LOG_LEVEL_DEBUG
            atomic_fetch_add_explicit(&g_refs_resize_total, 1, memory_order_relaxed);
#endif
            // wait until all users gone
            while (tbl->refs_control != 0x80000000) continue;
            break;
        }
    }

    tbl->refs_resize_table = tbl->refs_table;
    tbl->refs_resize_size = tbl->refs_size;
    tbl->refs_resize_part = 0;
    tbl->refs_resize_done = 0;

    // calculate new size
    size_t new_size = tbl->refs_size;
    size_t count = refs_count(tbl);
    if (count*4 > tbl->refs_size) new_size *= 2;

    // allocate new table
    _Atomic(uint64_t)* new_table = (_Atomic(uint64_t)*)alloc_aligned(new_size * sizeof(uint64_t));
    if (new_table == 0) {
        fprintf(stderr, "refs: Unable to allocate memory: %s!\n", strerror(errno));
        exit(1);
    }

    // set new data and go
    tbl->refs_table = new_table;
    tbl->refs_size = new_size;
    compiler_barrier();
    tbl->refs_control = 0x40000000;

    // until all parts are done, rehash blocks
    while (tbl->refs_resize_done != tbl->refs_resize_size/128) refs_resize_help(tbl);

    // done!
    compiler_barrier();
    tbl->refs_control = 0;

    // unmap old table
    free_aligned(tbl->refs_resize_table, tbl->refs_resize_size * sizeof(uint64_t));
}

/* Enter refs_modify */
static inline void
refs_enter(refs_table_t *tbl)
{
    for (;;) {
        uint32_t v = tbl->refs_control;
        if (v & 0xf0000000) {
            while (refs_resize_help(tbl)) continue;
        } else {
            if (atomic_compare_exchange_weak(&tbl->refs_control, &v, v+1)) return;
        }
    }
}

/* Leave refs_modify */
static inline void
refs_leave(refs_table_t *tbl)
{
    for (;;) {
        uint32_t v = tbl->refs_control;
        if (atomic_compare_exchange_weak(&tbl->refs_control, &v, v-1)) return;
    }
}

static inline int
refs_modify(refs_table_t *tbl, const uint64_t a, const int dir)
{
    _Atomic(uint64_t)* bucket;
    _Atomic(uint64_t)* ts_bucket;
    uint64_t v, new_v;
    int res, i;
#ifdef SYLVAN_REFS_STATS
    refs_stats_entry_t *stats = refs_stats_get(tbl);
    int probe_count = 0;
    uint64_t retry_count = 0;
    uint64_t update_count = 0;
    uint64_t miss_count = 0;
    uint64_t sample_ns = 0;
    uint64_t sample_count = 0;
    int do_sample = 0;
    struct timespec t0;
    if (stats) {
        uint64_t tick = refs_stats_next_tick();
        if ((tick & SYLVAN_REFS_STATS_TIME_SAMPLE_MASK) == 0) {
            do_sample = 1;
            clock_gettime(CLOCK_MONOTONIC, &t0);
        }
        atomic_fetch_add_explicit(&stats->modify_calls, 1, memory_order_relaxed);
        if (dir > 0) atomic_fetch_add_explicit(&stats->ups, 1, memory_order_relaxed);
        else atomic_fetch_add_explicit(&stats->downs, 1, memory_order_relaxed);
    }
#endif

    refs_enter(tbl);

ref_retry:
    bucket = tbl->refs_table + (fnvhash8(a) & (tbl->refs_size - 1));
    ts_bucket = NULL; // tombstone
    i = 128; // try 128 times linear probing

    while (i--) {
#ifdef SYLVAN_REFS_STATS
        probe_count++;
#endif
ref_restart:
        v = *bucket;
        if (v == refs_ts) {
            if (ts_bucket == NULL) ts_bucket = bucket;
        } else if (v == 0) {
            // not found
            res = 0;
            if (ts_bucket != NULL) {
                bucket = ts_bucket;
                ts_bucket = NULL;
                v = refs_ts;
            }
            new_v = refs_pack_count(a, (int32_t)dir);
            goto ref_mod;
        } else if ((v & 0x000000ffffffffff) == a) {
            // found
            res = 1;
            int32_t count = refs_unpack_count(v);
            if ((dir > 0 && count == refs_count_max) ||
                (dir < 0 && count == refs_count_min)) {
                goto ref_exit;
            }
            count += dir;
            if (count == 0) new_v = refs_ts;
            else new_v = refs_pack_count(a, count);
            goto ref_mod;
        }

        if (++bucket == tbl->refs_table + tbl->refs_size) bucket = tbl->refs_table;
    }

    // not found after linear probing
    if (ts_bucket != NULL) {
        bucket = ts_bucket;
        ts_bucket = NULL;
        v = refs_ts;
        new_v = refs_pack_count(a, (int32_t)dir);
        if (!atomic_compare_exchange_weak(bucket, &v, new_v)) {
#ifdef SYLVAN_REFS_STATS
            retry_count++;
            if (stats) atomic_fetch_add_explicit(&stats->retries, 1, memory_order_relaxed);
#endif
            goto ref_retry;
        }
        res = 1;
        goto ref_exit;
    } else {
        // hash table full
        refs_leave(tbl);
        refs_resize(tbl);
        return refs_modify(tbl, a, dir);
    }

ref_mod:
    if (!atomic_compare_exchange_weak(bucket, &v, new_v)) {
#ifdef SYLVAN_REFS_STATS
        retry_count++;
        if (stats) atomic_fetch_add_explicit(&stats->retries, 1, memory_order_relaxed);
#endif
        goto ref_restart;
    }
#ifdef SYLVAN_REFS_STATS
    if (stats) {
        atomic_fetch_add_explicit(&stats->updates, 1, memory_order_relaxed);
        size_t idx = (size_t)(bucket - tbl->refs_table);
        atomic_fetch_add_explicit(&stats->bucket_hist[idx & (SYLVAN_REFS_STATS_BUCKETS - 1)], 1, memory_order_relaxed);
    }
    update_count = 1;
#endif

ref_exit:
#ifdef SYLVAN_REFS_STATS
    if (stats) {
        if (do_sample) {
            struct timespec t1;
            clock_gettime(CLOCK_MONOTONIC, &t1);
            sample_ns = refs_stats_timespec_diff_ns(&t0, &t1);
            sample_count = 1;
            atomic_fetch_add_explicit(&stats->time_ns, sample_ns, memory_order_relaxed);
            atomic_fetch_add_explicit(&stats->time_samples, 1, memory_order_relaxed);
        }
        if (res == 0) {
            miss_count = 1;
            atomic_fetch_add_explicit(&stats->misses, 1, memory_order_relaxed);
        }
        atomic_fetch_add_explicit(&stats->probes, (uint64_t)probe_count, memory_order_relaxed);
        refs_stats_thread_add(stats, dir, (uint64_t)probe_count, retry_count,
                              miss_count, update_count, sample_ns, sample_count);
    }
#endif
    refs_leave(tbl);
    return res;
}

void
refs_up(refs_table_t *tbl, uint64_t a)
{
    refs_modify(tbl, a, 1);
}

void
refs_down(refs_table_t *tbl, uint64_t a)
{
    refs_modify(tbl, a, -1);
}

uint64_t*
refs_iter(refs_table_t *tbl, size_t first, size_t end)
{
    // assert(first < tbl->refs_size);
    // assert(end <= tbl->refs_size);

    _Atomic(uint64_t)* bucket = tbl->refs_table + first;
    while (bucket != tbl->refs_table + end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) return (uint64_t*)bucket;
        bucket++;
    }
    return NULL;
}

uint64_t
refs_next(refs_table_t *tbl, uint64_t **_bucket, size_t end)
{
    _Atomic(uint64_t)* bucket = (_Atomic(uint64_t)*)*_bucket;
    // assert(bucket != NULL);
    // assert(end <= tbl->refs_size);
    uint64_t result = atomic_load_explicit(bucket, memory_order_relaxed) & 0x000000ffffffffff;
    bucket++;
    while (bucket != tbl->refs_table + end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) {
            *_bucket = (uint64_t*)bucket;
            return result;
        }
        bucket++;
    }
    *_bucket = NULL;
    return result;
}

uint64_t
refs_next_full(refs_table_t *tbl, uint64_t **_bucket, size_t end, int32_t *count_out)
{
    _Atomic(uint64_t)* bucket = (_Atomic(uint64_t)*)*_bucket;
    uint64_t v = atomic_load_explicit(bucket, memory_order_relaxed);
    uint64_t result = v & 0x000000ffffffffff;
    if (count_out) *count_out = refs_unpack_count(v);
    bucket++;
    while (bucket != tbl->refs_table + end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) {
            *_bucket = (uint64_t*)bucket;
            return result;
        }
        bucket++;
    }
    *_bucket = NULL;
    return result;
}

void
refs_create(refs_table_t *tbl, size_t _refs_size)
{
    if (__builtin_popcountll(_refs_size) != 1) {
        fprintf(stderr, "refs: Table size must be a power of 2!\n");
        exit(1);
    }

    tbl->refs_size = _refs_size;
    tbl->refs_table = (_Atomic(uint64_t)*)alloc_aligned(tbl->refs_size * sizeof(uint64_t));
    if (tbl->refs_table == 0) {
        fprintf(stderr, "refs: Unable to allocate memory: %s!\n", strerror(errno));
        exit(1);
    }
    memset(tbl->refs_table, 0, tbl->refs_size * sizeof(uint64_t));
    atomic_store_explicit(&tbl->refs_control, 0, memory_order_relaxed);
    tbl->refs_resize_table = 0;
    tbl->refs_resize_size = 0;
    atomic_store_explicit(&tbl->refs_resize_part, 0, memory_order_relaxed);
    atomic_store_explicit(&tbl->refs_resize_done, 0, memory_order_relaxed);
#ifdef SYLVAN_REFS_STATS
    tbl->stats = NULL;
#endif
}

void
refs_free(refs_table_t *tbl)
{
    free_aligned(tbl->refs_table, tbl->refs_size * sizeof(uint64_t));
}

void
refs_clear(refs_table_t *tbl)
{
    memset(tbl->refs_table, 0, tbl->refs_size * sizeof(uint64_t));
}

int
refs_set_add(refs_table_t *tbl, uint64_t key, int32_t delta)
{
    _Atomic(uint64_t)* bucket = tbl->refs_table + (fnvhash8(key) & (tbl->refs_size - 1));
    _Atomic(uint64_t)* ts_bucket = NULL;
    int i = 128;

    while (i--) {
        uint64_t v = *bucket;
        if (v == refs_ts) {
            if (ts_bucket == NULL) ts_bucket = bucket;
        } else if (v == 0) {
            if (ts_bucket != NULL) {
                bucket = ts_bucket;
                ts_bucket = NULL;
            }
            *bucket = refs_pack_count(key, delta);
            return 1;
        } else if ((v & 0x000000ffffffffff) == key) {
            int32_t count = refs_unpack_count(v);
            if ((delta > 0 && count == refs_count_max) ||
                (delta < 0 && count == refs_count_min)) {
                return 0;
            }
            count += delta;
            if (count == 0) *bucket = refs_ts;
            else *bucket = refs_pack_count(key, count);
            return 1;
        }
        if (++bucket == tbl->refs_table + tbl->refs_size) bucket = tbl->refs_table;
    }
    return 0;
}

/**
 * Simple implementation of a 64-bit resizable hash-table
 * No idea if this is scalable... :( but it seems thread-safe
 */

// Count number of unique entries (not number of references)
size_t
protect_count(refs_table_t *tbl)
{
    size_t count = 0;
    _Atomic(uint64_t)* bucket = tbl->refs_table;
    _Atomic(uint64_t)* const end = bucket + tbl->refs_size;
    while (bucket != end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) count++;
        bucket++;
    }
    return count;
}

static inline void
protect_rehash(refs_table_t *tbl, uint64_t v)
{
    if (v == 0) return; // do not rehash empty value
    if (v == refs_ts) return; // do not rehash tombstone

    _Atomic(uint64_t)* bucket = tbl->refs_table + (fnvhash8(v) % tbl->refs_size);
    _Atomic(uint64_t)* const end = tbl->refs_table + tbl->refs_size;

    int i = 128; // try 128 times linear probing
    while (i--) {
        uint64_t d = atomic_load(bucket);
        if (d == 0 && atomic_compare_exchange_strong(bucket, &d, v)) return;
        if (++bucket == end) bucket = tbl->refs_table;
    }

    assert(0); // whoops!
}

/**
 * Called internally to assist resize operations
 * Returns 1 for retry, 0 for done
 */
static int
protect_resize_help(refs_table_t *tbl)
{
    if (0 == (tbl->refs_control & 0xf0000000)) return 0; // no resize in progress (anymore)
    if (tbl->refs_control & 0x80000000) return 1; // still waiting for preparation
    if (tbl->refs_resize_part >= tbl->refs_resize_size / 128) return 1; // all parts claimed
    size_t part = atomic_fetch_add(&tbl->refs_resize_part, 1);
    if (part >= tbl->refs_resize_size/128) return 1; // all parts claimed

    // rehash all
    int i;
    _Atomic(uint64_t)* bucket = tbl->refs_resize_table + part * 128;
    for (i=0; i<128; i++) protect_rehash(tbl, *bucket++);

    atomic_fetch_add(&tbl->refs_resize_done, 1);
    return 1;
}

static void
protect_resize(refs_table_t *tbl)
{
    while (1) {
        uint32_t v = tbl->refs_control;
        if (v & 0xf0000000) {
            // someone else started resize
            // just rehash blocks until done
            while (protect_resize_help(tbl)) continue;
            return;
        }
        if (atomic_compare_exchange_weak(&tbl->refs_control, &v, 0x80000000 | v)) {
#if MTPNDD_LOG_LEVEL >= MTPNDD_LOG_LEVEL_DEBUG
            atomic_fetch_add_explicit(&g_protect_resize_total, 1, memory_order_relaxed);
#endif
            // wait until all users gone
            while (tbl->refs_control != 0x80000000) continue;
            break;
        }
    }

    tbl->refs_resize_table = tbl->refs_table;
    tbl->refs_resize_size = tbl->refs_size;
    tbl->refs_resize_part = 0;
    tbl->refs_resize_done = 0;

    // calculate new size
    size_t new_size = tbl->refs_size;
    size_t count = refs_count(tbl);
    if (count*4 > tbl->refs_size) new_size *= 2;

    // allocate new table
    _Atomic(uint64_t)* new_table = (_Atomic(uint64_t)*)alloc_aligned(new_size * sizeof(uint64_t));
    if (new_table == 0) {
        fprintf(stderr, "refs: Unable to allocate memory: %s!\n", strerror(errno));
        exit(1);
    }

    // set new data and go
    tbl->refs_table = new_table;
    tbl->refs_size = new_size;
    compiler_barrier();
    tbl->refs_control = 0x40000000;

    // until all parts are done, rehash blocks
    while (tbl->refs_resize_done < tbl->refs_resize_size/128) protect_resize_help(tbl);

    // done!
    compiler_barrier();
    tbl->refs_control = 0;

    // unmap old table
    free_aligned(tbl->refs_resize_table, tbl->refs_resize_size * sizeof(uint64_t));
}

static inline void
protect_enter(refs_table_t *tbl)
{
    for (;;) {
        uint32_t v = tbl->refs_control;
        if (v & 0xf0000000) {
            while (protect_resize_help(tbl)) continue;
        } else {
            if (atomic_compare_exchange_weak(&tbl->refs_control, &v, v+1)) return;
        }
    }
}

static inline void
protect_leave(refs_table_t *tbl)
{
    for (;;) {
        uint32_t v = tbl->refs_control;
        if (atomic_compare_exchange_weak(&tbl->refs_control, &v, v-1)) return;
    }
}

void
protect_up(refs_table_t *tbl, uint64_t a)
{
    _Atomic(uint64_t)* bucket;
    _Atomic(uint64_t)* ts_bucket;
    uint64_t v;
    int i;

    protect_enter(tbl);

ref_retry:
    bucket = tbl->refs_table + (fnvhash8(a) & (tbl->refs_size - 1));
    ts_bucket = NULL; // tombstone
    i = 128; // try 128 times linear probing

    while (i--) {
ref_restart:
        v = *bucket;
        if (v == a) {
            // Already present in this table: set semantics, no extra insert needed.
            protect_leave(tbl);
            return;
        } else if (v == refs_ts) {
            if (ts_bucket == NULL) ts_bucket = bucket;
        } else if (v == 0) {
            // go go go
            if (ts_bucket != NULL) {
                v = refs_ts;
                if (atomic_compare_exchange_weak(ts_bucket, &v, a)) {
                    protect_leave(tbl);
                    return;
                } else {
                    goto ref_retry;
                }
            } else {
                if (atomic_compare_exchange_weak(bucket, &v, a)) {
                    protect_leave(tbl);
                    return;
                } else {
                    goto ref_restart;
                }
            }
        }

        if (++bucket == tbl->refs_table + tbl->refs_size) bucket = tbl->refs_table;
    }

    // not found after linear probing
    if (ts_bucket != NULL) {
        v = refs_ts;
        if (atomic_compare_exchange_weak(ts_bucket, &v, a)) {
            protect_leave(tbl);
            return;
        } else {
            goto ref_retry;
        }
    } else {
        // hash table full
        protect_leave(tbl);
        protect_resize(tbl);
        protect_enter(tbl);
        goto ref_retry;
    }
}

void
protect_add_insert(refs_table_t *tbl, uint64_t a)
{
    protect_up(tbl, a);
}

int
protect_add_remove_one(refs_table_t *tbl, uint64_t a)
{
    _Atomic(uint64_t)* bucket;
    protect_enter(tbl);

    bucket = tbl->refs_table + (fnvhash8(a) & (tbl->refs_size - 1));
    int i = 128; // try 128 times linear probing

    while (i--) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d == a) {
            atomic_store_explicit(bucket, refs_ts, memory_order_relaxed);
            protect_leave(tbl);
            return 1;
        }
        if (++bucket == tbl->refs_table + tbl->refs_size) bucket = tbl->refs_table;
    }

    protect_leave(tbl);
    return 0;
}

void
protect_del_insert(refs_table_t *tbl, uint64_t a)
{
    protect_up(tbl, a);
}

void
protect_down(refs_table_t *tbl, uint64_t a)
{
    _Atomic(uint64_t)* bucket;
    protect_enter(tbl);

    bucket = tbl->refs_table + (fnvhash8(a) & (tbl->refs_size - 1));
    int i = 128; // try 128 times linear probing

    while (i--) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d == a) {
            atomic_store_explicit(bucket, refs_ts, memory_order_relaxed);
            protect_leave(tbl);
            return;
        }
        if (++bucket == tbl->refs_table + tbl->refs_size) bucket = tbl->refs_table;
    }

    // not found after linear probing
    assert(0);
}

uint64_t*
protect_iter(refs_table_t *tbl, size_t first, size_t end)
{
    // assert(first < tbl->refs_size);
    // assert(end <= tbl->refs_size);

    _Atomic(uint64_t)* bucket = tbl->refs_table + first;
    while (bucket != tbl->refs_table + end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) return (uint64_t*)bucket;
        bucket++;
    }
    return NULL;
}

uint64_t
protect_next(refs_table_t *tbl, uint64_t **_bucket, size_t end)
{
    _Atomic(uint64_t)* bucket = (_Atomic(uint64_t)*) *_bucket;
    // assert(bucket != NULL);
    // assert(end <= tbl->refs_size);
    uint64_t result = *bucket;
    bucket++;
    while (bucket != tbl->refs_table + end) {
        uint64_t d = atomic_load_explicit(bucket, memory_order_relaxed);
        if (d != 0 && d != refs_ts) {
            *_bucket = (uint64_t*)bucket;
            return result;
        }
        bucket++;
    }
    *_bucket = NULL;
    return result;
}

void
protect_create(refs_table_t *tbl, size_t _refs_size)
{
    if (__builtin_popcountll(_refs_size) != 1) {
        fprintf(stderr, "refs: Table size must be a power of 2!\n");
        exit(1);
    }

    tbl->refs_size = _refs_size;
    tbl->refs_table = (_Atomic(uint64_t)*)alloc_aligned(tbl->refs_size * sizeof(uint64_t));
    if (tbl->refs_table == 0) {
        fprintf(stderr, "refs: Unable to allocate memory: %s!\n", strerror(errno));
        exit(1);
    }
    memset(tbl->refs_table, 0, tbl->refs_size * sizeof(uint64_t));
    atomic_store_explicit(&tbl->refs_control, 0, memory_order_relaxed);
    tbl->refs_resize_table = 0;
    tbl->refs_resize_size = 0;
    atomic_store_explicit(&tbl->refs_resize_part, 0, memory_order_relaxed);
    atomic_store_explicit(&tbl->refs_resize_done, 0, memory_order_relaxed);
#ifdef SYLVAN_REFS_STATS
    tbl->stats = NULL;
#endif
}

void
protect_free(refs_table_t *tbl)
{
    free_aligned(tbl->refs_table, tbl->refs_size * sizeof(uint64_t));
    tbl->refs_table = 0;
}
