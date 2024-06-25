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

private enum Permission { CannotSee, Use, Edit, Own }

sig Group {
    // A Group has 0 or 1 explicitly granted permissions to each Object
    // Not using the `var` keyword because explicit permissions won't change over
    // the course of a simulation
    explicit: Permission lone -> set Object,
}

run make_filesystem {
} for exactly 2 Folder, exactly 1 App, exactly 1 Group
