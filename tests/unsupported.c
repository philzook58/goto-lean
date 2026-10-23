int global;
int global_read(void) { return global; }
int global_write(void) { global = 1; return global; }
int pointers(int *x) { return *x; }
float floating(float x) { return x + 1; }
extern int helper(int);
int calls(int x) { return helper(x); }
int indirect(int x) { int (*p)(int) = helper; return p(x); }
struct pair { int x, y; };
int structs(struct pair p) { return p.x; }
int statics(void) { static int n; return ++n; }
int initialized = 17;
int global_roundtrip(void) {
    global = initialized;
    initialized = global_read() + 1;
    return initialized + global;
}
int global_memory(void) {
    global = 41;
    int x = 1;
    int *p = &x;
    *p += global_read();
    return global + *p;
}
int *global_address(void) { return &global; }

int static_roundtrip(void) { return statics() + statics(); }
