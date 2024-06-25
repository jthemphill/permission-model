open util/graph[Object] as object_graph

abstract sig Object {
    var private parent: lone Folder,
}

sig App extends Object {}

sig Folder extends Object {
    var children: set Object,
}

fact start_as_a_tree {
    object_graph/tree[children]
}

fact parent_is_opposite_of_children {
    always {
        all o: Object {
            o.parent = {f: Folder | o in f.children}
        }
    }
}

fun root_folder: one Folder {
    {f: Folder | no f.parent}
}

// Permissions, ordered from weakest to strongest.
// The lowest permission in Retool is "None", but `none` is a reserved keyword
// in Alloy. I'm going to use the term `CannotSee` throughout this spec instead.
private enum Permission { CannotSee, Use, Edit, Own }

run make_filesystem {
} for exactly 2 Folder, exactly 1 App
