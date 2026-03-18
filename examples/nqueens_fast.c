#include <getopt.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#define NOGDI
#include <windows.h>
#else
#include <unistd.h>
#endif

#include <sylvan.h>
#include <sylvan_stats.h>
#include <sylvan_table.h>

static int workers = 0;
static size_t board_size = 0;

static void
parse_args(int argc, char **argv)
{
    static const struct option longopts[] = {
        {.name = "workers", .val = 'w', .has_arg = required_argument},
        {.name = "help", .val = 'h', .has_arg = no_argument},
        {},
    };
    int key = 0;
    while ((key = getopt_long(argc, argv, "w:h", longopts, NULL)) != -1) {
        switch (key) {
        case 'w':
            workers = atoi(optarg);
            break;
        case 'h':
        default:
            fprintf(stderr, "Usage: nqueens_fast [-w workers] <size>\n");
            exit(key == 'h' ? 0 : -1);
        }
    }
    if (optind >= argc) {
        fprintf(stderr, "Missing board size\n");
        exit(-1);
    }
    board_size = strtoull(argv[optind], NULL, 10);
    if (board_size == 0) {
        fprintf(stderr, "Board size must be > 0\n");
        exit(-1);
    }
}

static inline BDD
implies_not(BDD a, BDD b)
{
    return sylvan_or(sylvan_not(a), sylvan_not(b));
}

static uint64_t
gibibytes(uint64_t value)
{
    return value * 1024ULL * 1024ULL * 1024ULL;
}

static uint64_t
configured_memory_cap(void)
{
    const char *env = getenv("NQUEENS_SYLVAN_MEMORY_CAP_MB");
    if (env == NULL || *env == '\0') return 0;

    char *end = NULL;
    unsigned long long value = strtoull(env, &end, 10);
    if (end == env || *end != '\0' || value == 0) {
        fprintf(stderr, "Ignoring invalid NQUEENS_SYLVAN_MEMORY_CAP_MB=%s\n", env);
        return 0;
    }

    return (uint64_t)value * 1024ULL * 1024ULL;
}

static uint64_t
detected_physical_memory(void)
{
#if defined(_WIN32)
    MEMORYSTATUSEX status;
    status.dwLength = sizeof(status);
    if (!GlobalMemoryStatusEx(&status)) return 0;
    return (uint64_t)status.ullTotalPhys;
#else
    long pages = sysconf(_SC_PHYS_PAGES);
    long page_size = sysconf(_SC_PAGE_SIZE);
    if (pages <= 0 || page_size <= 0) return 0;
    return (uint64_t)pages * (uint64_t)page_size;
#endif
}

static uint64_t
choose_memory_cap(void)
{
    uint64_t configured = configured_memory_cap();
    if (configured != 0) return configured;

    uint64_t requested = board_size >= 12 ? gibibytes(10) :
        board_size >= 11 ? gibibytes(6) :
        gibibytes(3);

    uint64_t physical = detected_physical_memory();
    if (physical != 0) {
        uint64_t safe_cap = physical * 3 / 4;
        uint64_t minimum_cap = 1024ULL * 1024ULL * 1024ULL;
        if (safe_cap < minimum_cap) safe_cap = minimum_cap;
        if (requested > safe_cap) requested = safe_cap;
    }

    return requested;
}

int
main(int argc, char **argv)
{
    parse_args(argc, argv);

    lace_start(workers, 1000000);

    /*
     * Use Sylvan's limit-based sizing instead of hard-coding large tables.
     * The old n>=11 tier jumped straight to ~8.25 GiB of node+cache capacity,
     * which easily turns into swapping or OOM on modest machines.
     */
    sylvan_set_limits(choose_memory_cap(), 2, 5);
    sylvan_init_package();
    sylvan_init_bdd();

    BDD *board = malloc(sizeof(BDD) * board_size * board_size);
    for (size_t i = 0; i < board_size * board_size; i++) {
        board[i] = sylvan_ithvar(i);
        sylvan_protect(board + i);
    }

    BDD res = sylvan_true;
    sylvan_protect(&res);

    // Each row must contain at least one queen
    for (size_t i = 0; i < board_size; i++) {
        BDD clause = sylvan_false;
        sylvan_protect(&clause);
        for (size_t j = 0; j < board_size; j++) {
            clause = sylvan_or(clause, board[i*board_size + j]);
        }
        res = sylvan_and(res, clause);
        sylvan_unprotect(&clause);
    }

    // Per-cell constraints (columns and both diagonals)
    for (size_t i = 0; i < board_size; i++) {
        for (size_t j = 0; j < board_size; j++) {
            size_t idx = i*board_size + j;
            BDD target = board[idx];

            BDD a = sylvan_true;
            BDD b = sylvan_true;
            BDD c = sylvan_true;
            BDD d = sylvan_true;
            sylvan_protect(&a);
            sylvan_protect(&b);
            sylvan_protect(&c);
            sylvan_protect(&d);

            for (size_t col = 0; col < board_size; col++) {
                if (col == j) continue;
                a = sylvan_and(a, implies_not(target, board[i*board_size + col]));
            }

            for (size_t row = 0; row < board_size; row++) {
                if (row == i) continue;
                b = sylvan_and(b, implies_not(target, board[row*board_size + j]));
            }

            for (size_t row = 0; row < board_size; row++) {
                size_t col = row - i + j;
                if (row == i || col >= board_size) continue;
                c = sylvan_and(c, implies_not(target, board[row*board_size + col]));
            }

            for (size_t row = 0; row < board_size; row++) {
                ssize_t col = (ssize_t)i + (ssize_t)j - (ssize_t)row;
                if (row == i || col < 0 || (size_t)col >= board_size) continue;
                d = sylvan_and(d, implies_not(target, board[row*board_size + (size_t)col]));
            }

            BDD local = sylvan_and(a, b);
            local = sylvan_and(local, c);
            local = sylvan_and(local, d);
            res = sylvan_and(res, local);

            sylvan_unprotect(&a);
            sylvan_unprotect(&b);
            sylvan_unprotect(&c);
            sylvan_unprotect(&d);
        }
    }

    // Build cube of variables for satcount
    BDD vars = sylvan_true;
    sylvan_protect(&vars);
    for (size_t i = 0; i < board_size * board_size; i++) {
        vars = sylvan_and(vars, board[i]);
    }

    double solutions = sylvan_satcount(res, vars);

    sylvan_stats_t snapshot;
    sylvan_stats_snapshot(&snapshot);
    uint64_t nodes_created = snapshot.counters[BDD_NODES_CREATED];
    size_t nodes_alive = sylvan_nodecount(res);

    printf("NQUEENS_METRICS n=%zu solutions=%.0f nodes_created=%" PRIu64 " nodes_alive=%zu\n",
        board_size, solutions, nodes_created, nodes_alive);

    sylvan_unprotect(&vars);
    sylvan_unprotect(&res);
    for (size_t i = 0; i < board_size * board_size; i++) {
        sylvan_unprotect(board + i);
    }

    sylvan_quit();
    lace_stop();
    free(board);
    return 0;
}
