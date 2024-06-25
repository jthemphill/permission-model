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
    explicit: Permission lone -> set Object,
}

// For now, we use only one User.
one sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    // This relation represents the calculated level of access the User has to
    // each Object.
    var calculated: Permission one -> Object,
}

run make_filesystem {
} for exactly 2 Folder, exactly 1 App, exactly 1 Group
