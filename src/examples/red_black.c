enum rb_color {
    red,
    black
};

struct rb_tree {
    enum rb_color color;

    int key;
    struct rb_tree* left;
    struct rb_tree* right;
};
