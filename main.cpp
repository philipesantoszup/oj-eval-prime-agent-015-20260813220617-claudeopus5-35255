
#include <cstdio>
#include <cstring>
#include <cstdlib>

struct Key {
    char s[68];
    int v;
};

static inline int kcmp(const Key &a, const Key &b) {
    int c = strcmp(a.s, b.s);
    if (c) return c;
    return (a.v < b.v) ? -1 : (a.v > b.v ? 1 : 0);
}

const int MAXK = 63;
struct Node {
    int isLeaf;
    int cnt;
    int next;
    int prev;
    int child[MAXK + 2];
    Key key[MAXK + 1];
};

const long HDR = 4096;
static FILE *fp = 0;
static int pageCount = 1;
static int freeHead = -1;

const int SLOTS = 64;
static Node buf[SLOTS];
static int slotPage[SLOTS];
static char slotDirty[SLOTS];

static inline int slotOf(int p) {
    if (p == 0) return 0;
    return 1 + (p - 1) % (SLOTS - 1);
}
static inline long offOf(int p) { return HDR + (long)p * (long)sizeof(Node); }

static void flushSlot(int s) {
    if (slotPage[s] >= 0 && slotDirty[s]) {
        fseek(fp, offOf(slotPage[s]), SEEK_SET);
        fwrite(&buf[s], sizeof(Node), 1, fp);
        slotDirty[s] = 0;
    }
}

static Node *getNode(int p) {
    int s = slotOf(p);
    if (slotPage[s] == p) return &buf[s];
    flushSlot(s);
    fseek(fp, offOf(p), SEEK_SET);
    if (fread(&buf[s], sizeof(Node), 1, fp) != 1) memset(&buf[s], 0, sizeof(Node));
    slotPage[s] = p;
    slotDirty[s] = 0;
    return &buf[s];
}
static inline void markDirty(int p) {
    int s = slotOf(p);
    if (slotPage[s] == p) slotDirty[s] = 1;
}
static void putNode(int p, const Node &n) {
    int s = slotOf(p);
    if (slotPage[s] != p) flushSlot(s);
    memcpy(&buf[s], &n, sizeof(Node));
    slotPage[s] = p;
    slotDirty[s] = 1;
}

static int allocPage() {
    if (freeHead >= 0) {
        int p = freeHead;
        Node *n = getNode(p);
        freeHead = n->next;
        return p;
    }
    return pageCount++;
}
static void freePage(int p) {
    Node *n = getNode(p);
    memset(n, 0, sizeof(Node));
    n->next = freeHead;
    n->prev = -1;
    markDirty(p);
    freeHead = p;
}

static void writeHeader() {
    fseek(fp, 0, SEEK_SET);
    int hdr[4];
    hdr[0] = 0x42505432;
    hdr[1] = pageCount;
    hdr[2] = freeHead;
    hdr[3] = 0;
    fwrite(hdr, sizeof(int), 4, fp);
}
static void flushAll() {
    for (int s = 0; s < SLOTS; s++) flushSlot(s);
    writeHeader();
    fflush(fp);
}

static void initEmpty() {
    for (int s = 0; s < SLOTS; s++) { slotPage[s] = -1; slotDirty[s] = 0; }
    pageCount = 1;
    freeHead = -1;
    Node r;
    memset(&r, 0, sizeof(Node));
    r.isLeaf = 1; r.cnt = 0; r.next = -1; r.prev = -1;
    putNode(0, r);
    flushAll();
}

static void openDB(const char *name) {
    fp = fopen(name, "rb+");
    if (!fp) {
        fp = fopen(name, "wb+");
        if (!fp) exit(1);
        initEmpty();
        return;
    }
    for (int s = 0; s < SLOTS; s++) { slotPage[s] = -1; slotDirty[s] = 0; }
    int hdr[4];
    fseek(fp, 0, SEEK_SET);
    if (fread(hdr, sizeof(int), 4, fp) != 4 || hdr[0] != 0x42505432) {
        fclose(fp);
        fp = fopen(name, "wb+");
        if (!fp) exit(1);
        initEmpty();
        return;
    }
    pageCount = hdr[1];
    freeHead = hdr[2];
    if (pageCount < 1) pageCount = 1;
}

static int pathPage[40];
static int pathIdx[40];

static void bptInsert(const Key &k) {
    int depth = 0;
    int p = 0;
    while (true) {
        Node *n = getNode(p);
        if (n->isLeaf) break;
        int c = n->cnt;
        int i = 0;
        while (i < c - 1 && kcmp(n->key[i], k) <= 0) i++;
        pathPage[depth] = p;
        pathIdx[depth] = i;
        depth++;
        p = n->child[i];
    }
    {
        Node *L = getNode(p);
        int lo = 0, hi = L->cnt;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            if (kcmp(L->key[mid], k) < 0) lo = mid + 1; else hi = mid;
        }
        int i = lo;
        if (i < L->cnt && kcmp(L->key[i], k) == 0) return;
        for (int j = L->cnt; j > i; j--) L->key[j] = L->key[j - 1];
        L->key[i] = k;
        L->cnt++;
        markDirty(p);
        if (L->cnt <= MAXK) return;
    }
    Key sep;
    int np = allocPage();
    {
        Node R;
        memset(&R, 0, sizeof(Node));
        Node *L = getNode(p);
        int mid = L->cnt / 2;
        R.isLeaf = 1;
        R.cnt = L->cnt - mid;
        memcpy(R.key, L->key + mid, (size_t)R.cnt * sizeof(Key));
        R.next = L->next;
        R.prev = p;
        L->cnt = mid;
        L->next = np;
        markDirty(p);
        sep = R.key[0];
        int rn = R.next;
        putNode(np, R);
        if (rn >= 0) { Node *N = getNode(rn); N->prev = np; markDirty(rn); }
    }
    for (int d = depth - 1; d >= 0; d--) {
        int q = pathPage[d];
        int i = pathIdx[d];
        bool overflow;
        {
            Node *n = getNode(q);
            for (int j = n->cnt - 1; j > i; j--) n->child[j + 1] = n->child[j];
            n->child[i + 1] = np;
            for (int j = n->cnt - 2; j >= i; j--) n->key[j + 1] = n->key[j];
            n->key[i] = sep;
            n->cnt++;
            markDirty(q);
            overflow = (n->cnt > MAXK + 1);
        }
        if (!overflow) return;
        int np2 = allocPage();
        Node R;
        memset(&R, 0, sizeof(Node));
        Key up;
        {
            Node *n = getNode(q);
            int m = n->cnt / 2 - 1;
            up = n->key[m];
            R.isLeaf = 0;
            R.next = -1; R.prev = -1;
            R.cnt = n->cnt - (m + 1);
            memcpy(R.child, n->child + m + 1, (size_t)R.cnt * sizeof(int));
            memcpy(R.key, n->key + m + 1, (size_t)(R.cnt - 1) * sizeof(Key));
            n->cnt = m + 1;
            markDirty(q);
        }
        putNode(np2, R);
        sep = up;
        np = np2;
    }
    {
        Node tmp;
        memcpy(&tmp, getNode(0), sizeof(Node));
        int rp = allocPage();
        putNode(rp, tmp);
        if (tmp.isLeaf) {
            if (tmp.next >= 0) { Node *N = getNode(tmp.next); N->prev = rp; markDirty(tmp.next); }
            if (tmp.prev >= 0) { Node *N = getNode(tmp.prev); N->next = rp; markDirty(tmp.prev); }
        }
        Node nr;
        memset(&nr, 0, sizeof(Node));
        nr.isLeaf = 0; nr.next = -1; nr.prev = -1;
        nr.cnt = 2;
        nr.child[0] = rp;
        nr.child[1] = np;
        nr.key[0] = sep;
        putNode(0, nr);
    }
}

static void bptErase(const Key &k) {
    int depth = 0;
    int p = 0;
    while (true) {
        Node *n = getNode(p);
        if (n->isLeaf) break;
        int c = n->cnt;
        int i = 0;
        while (i < c - 1 && kcmp(n->key[i], k) <= 0) i++;
        pathPage[depth] = p;
        pathIdx[depth] = i;
        depth++;
        p = n->child[i];
    }
    bool empty;
    {
        Node *L = getNode(p);
        int lo = 0, hi = L->cnt - 1, pos = -1;
        while (lo <= hi) {
            int mid = (lo + hi) >> 1;
            int c = kcmp(L->key[mid], k);
            if (c == 0) { pos = mid; break; }
            if (c < 0) lo = mid + 1; else hi = mid - 1;
        }
        if (pos < 0) return;
        for (int j = pos; j + 1 < L->cnt; j++) L->key[j] = L->key[j + 1];
        L->cnt--;
        markDirty(p);
        empty = (L->cnt == 0);
    }
    if (!empty || depth == 0) return;
    // unlink leaf from list
    {
        Node *L = getNode(p);
        int pv = L->prev, nx = L->next;
        if (pv >= 0) { Node *A = getNode(pv); A->next = nx; markDirty(pv); }
        if (nx >= 0) { Node *B = getNode(nx); B->prev = pv; markDirty(nx); }
    }
    freePage(p);
    // remove child pointer from ancestors
    int childToRemove = p;
    for (int d = depth - 1; d >= 0; d--) {
        int q = pathPage[d];
        Node *n = getNode(q);
        int i = -1;
        for (int j = 0; j < n->cnt; j++) if (n->child[j] == childToRemove) { i = j; break; }
        if (i < 0) return;
        int ki = (i > 0) ? (i - 1) : 0;
        for (int j = i; j + 1 < n->cnt; j++) n->child[j] = n->child[j + 1];
        for (int j = ki; j + 2 < n->cnt; j++) n->key[j] = n->key[j + 1];
        n->cnt--;
        markDirty(q);
        if (n->cnt > 0) return;
        if (d == 0) {
            // root became empty -> reset to empty leaf
            Node r;
            memset(&r, 0, sizeof(Node));
            r.isLeaf = 1; r.cnt = 0; r.next = -1; r.prev = -1;
            putNode(0, r);
            return;
        }
        freePage(q);
        childToRemove = q;
    }
}

static char obuf[1 << 14];
static int olen = 0;
static inline void oflush() { if (olen) { fwrite(obuf, 1, olen, stdout); olen = 0; } }
static inline void ochar(char c) { if (olen >= (int)sizeof(obuf) - 1) oflush(); obuf[olen++] = c; }
static inline void oint(int x) {
    char t[12]; int l = 0;
    if (x == 0) t[l++] = '0';
    while (x > 0) { t[l++] = (char)('0' + x % 10); x /= 10; }
    while (l > 0) ochar(t[--l]);
}
static inline void ostr(const char *s) { while (*s) ochar(*s++); }

static void bptFind(const char *index) {
    Key lb;
    memset(&lb, 0, sizeof(Key));
    strncpy(lb.s, index, 67);
    lb.v = -1;
    int p = 0;
    while (true) {
        Node *n = getNode(p);
        if (n->isLeaf) break;
        int c = n->cnt;
        int i = 0;
        while (i < c - 1 && kcmp(n->key[i], lb) <= 0) i++;
        p = n->child[i];
    }
    bool any = false;
    int start;
    {
        Node *L = getNode(p);
        int lo = 0, hi = L->cnt;
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            if (kcmp(L->key[mid], lb) < 0) lo = mid + 1; else hi = mid;
        }
        start = lo;
    }
    while (p >= 0) {
        Node *L = getNode(p);
        int c = L->cnt;
        int nxt = L->next;
        bool stop = false;
        for (int i = start; i < c; i++) {
            int cc = strcmp(L->key[i].s, index);
            if (cc < 0) continue;
            if (cc > 0) { stop = true; break; }
            if (any) ochar(' ');
            oint(L->key[i].v);
            any = true;
        }
        if (stop) break;
        start = 0;
        p = nxt;
    }
    if (!any) ostr("null");
    ochar('\n');
}

static char ibuf[1 << 14];
static int ipos = 0, ilen = 0;
static inline int gc() {
    if (ipos >= ilen) {
        ilen = (int)fread(ibuf, 1, sizeof(ibuf), stdin);
        ipos = 0;
        if (ilen <= 0) return -1;
    }
    return (unsigned char)ibuf[ipos++];
}
static bool readToken(char *dst, int cap) {
    int c = gc();
    while (c >= 0 && c <= 32) c = gc();
    if (c < 0) { dst[0] = 0; return false; }
    int l = 0;
    while (c > 32) {
        if (l < cap - 1) dst[l++] = (char)c;
        c = gc();
    }
    dst[l] = 0;
    return true;
}
static bool readInt(int &x) {
    int c = gc();
    while (c >= 0 && c <= 32) c = gc();
    if (c < 0) return false;
    int sgn = 1;
    if (c == '-') { sgn = -1; c = gc(); }
    long long r = 0;
    while (c >= '0' && c <= '9') { r = r * 10 + (c - '0'); c = gc(); }
    x = (int)(r * sgn);
    return true;
}

int main() {
    openDB("storage.db");
    int n;
    if (!readInt(n)) { flushAll(); fclose(fp); return 0; }
    char cmd[16];
    char idx[80];
    Key k;
    for (int t = 0; t < n; t++) {
        if (!readToken(cmd, sizeof(cmd))) break;
        if (cmd[0] == 'i') {
            readToken(idx, sizeof(idx));
            int v; readInt(v);
            memset(&k, 0, sizeof(Key));
            strncpy(k.s, idx, 67);
            k.v = v;
            bptInsert(k);
        } else if (cmd[0] == 'd') {
            readToken(idx, sizeof(idx));
            int v; readInt(v);
            memset(&k, 0, sizeof(Key));
            strncpy(k.s, idx, 67);
            k.v = v;
            bptErase(k);
        } else if (cmd[0] == 'f') {
            readToken(idx, sizeof(idx));
            bptFind(idx);
        }
    }
    oflush();
    fflush(stdout);
    flushAll();
    fclose(fp);
    return 0;
}
