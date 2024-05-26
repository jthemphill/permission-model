// Import a module with some properties about graphs and our Object sig, name it `object_graph`
open util/graph[Object] as object_graph

abstract sig Object {}

sig App extends Object {}

sig Folder extends Object {
    var children: set Object,
}

// A `fact` contains booleans that *must* be true. Alloy won't even try to simulate
// a universe where a fact wouldn't be true.
fact start_as_a_tree {
    // Ask the imported module if all our Objects are in a tree
    object_graph/tree[children]
}

// Now all the Objects should be in a tree structure!
run make_filesystem {
} for exactly 2 Folder, exactly 1 App
