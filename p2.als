// Import a module with some properties about graphs, name it `object_graph`
open util/graph[Object] as object_graph

abstract sig Object {}

sig App extends Object {}

sig Folder extends Object {
    // Folders can contain Apps and other Folders
    var children: set Object,
    var parent: lone Object,
}

// You should be able to execute this and see a picture of a filesystem!
run make_filesystem {
} for exactly 2 Folder, exactly 1 App

fact start_as_a_tree {
    object_graph/tree[children]
}

fact parent_is_opposite_of_children {
    always {
        all o: Object {
            no o.parent or o in o.parent.children
        }
    }
}

// Always returns exactly 1 folder
fun root_folder: one Folder {
    {f: Folder | no f.parent}
}

// Permissions, ordered from weakest to strongest.
// The lowest permission in Retool is "None", but `none` is a reserved keyword
// in Alloy. I'm going to use the term `CannotSee` throughout this spec instead.
enum Permission { CannotSee, Use, Edit, Own }

sig Group {
    // A Group has 0 or 1 explicitly granted permissions to each Object
    // Not using the `var` keyword because this shouldn't change over the course
    // of a simulation
    explicit: Permission lone -> set Object,
    implicit: Permission one -> set Object,
}

// You can add this to the bottom of your file, or scroll up and fix
// the original `make_filesystem` command instead
run make_filesystem_2 {
} for exactly 2 Folder, exactly 1 App, exactly 1 Group

// For now, we use only one User.
one sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    // This relation represents the calculated level of access the User has to
    // each Object.
    var calculated: Permission one -> Object,
}

fact calculate_user_permissions {
    always {
        all o: Object {
            // Return the greatest permission for an object across all of the User's groups
            let p = ordering/max[{ p: Permission | some g : User.groups | p = group_implicit[g, o] }] {
                o in User.calculated[p]
            }
        }
    }
}

// Return the Group's permission to the Object if there is one, or go up the tree
// and return the first inherited permission you see
fun group_implicit[g: Group, o: Object]: one Permission {
    group_implicit[g, parent[o]]
}

// fact calculate_user_implicit_permissions {
//     all object: Object |
//         let strongest_perm = ordering/max[{p: Permission | user_implicit[p, object]}] |
//             object in implicit[strongest_perm]
// }