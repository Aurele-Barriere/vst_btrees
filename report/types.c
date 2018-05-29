typedef struct Relation {
    struct BtNode* root;
    size_t numRecords;
    int depth;
} Relation;

union Child_or_Record {
    BtNode* child;
    const void* record;
};

struct Entry {
    Key key;
    Child_or_Record ptr;
};

struct BtNode {
    Bool isLeaf;
    Bool First;
    Bool Last;
    int numKeys;
    BtNode* ptr0;
    Entry entries[FANOUT];
};

struct Cursor {
    Relation* relation;
    int level;
    int ancestorsIdx[MAX_TREE_DEPTH];
    BtNode* ancestors[MAX_TREE_DEPTH];
};
