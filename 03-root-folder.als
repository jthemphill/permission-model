open util/graph[Object] as object_graph

abstract sig Object {
    // `private` keyword stops it from cluttering up the diagram
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

// Always returns the 1 folder that has no parents
fun root_folder: one Folder {
    {f: Folder | no f.parent}
}

// Now the root folder will be labeled!
run make_filesystem {
} for exactly 2 Folder, exactly 1 App
