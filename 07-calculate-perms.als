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
    var private implicit: Permission one -> set Object,
}

fact calculate_group_implicit_perms {
    always {
        all g: Group {
            all o: Object {
                some p : Permission {
                    o in g.implicit[p] <=> (
                        o in g.explicit[p] or
                        some ancestor : Folder {
                            ancestor in g.explicit[p]
                        }
                    )
                }
            }
        }
    }
}

one sig User {
    groups: set Group,
    var calculated: Permission one -> set Object,
}

run make_filesystem {
} for exactly 2 Folder, exactly 1 App, exactly 1 Group
