// Import a module with some properties about graphs
open util/graph[Object]

abstract sig Object {
    var parent: lone Folder,
}

sig App extends Object {}

sig Folder extends Object {
    // Folders can contain Apps and other Folders
    var children: set Object,
}

one sig RootFolder extends Folder {
}

fact root_folder_has_no_parent {
    always {
        no RootFolder.parent
    }
}

fact file_system_starts_as_a_tree {
    graph/treeRootedAt[children, RootFolder]
}

fact parent_is_inverse_of_children {
    always {
        parent = ~children
    }
}

// Permissions, ordered from weakest to strongest.
//
// The lowest permission in Retool is "None", but `none` is a reserved keyword
// in Alloy. I'm going to use the term `CannotSee` throughout this spec instead.
//
// Declaring an enum automatically imports the ordering module.
enum Permission { CannotSee, Use, Edit, Own }

sig Group {
    // A Group has 0 or 1 explicitly granted permissions to each Object
    // These shouldn't change over the course of a simulation.
    explicit: Permission lone -> set Object,
    // The explicit permissions result in calculated permissions,
    // which *do* change over the course of a simulation.
    var calculated: Permission one -> set Object,
}

fact calculate_group_permissions {
    always {
        all g: Group, o: Object {
            // A Group's calculated permission to the object is the maximum explicit permission we
            // find as we go up the tree.
            ~(g.calculated)[o] = ordering/max[~(g.explicit)[o.*parent] + CannotSee]
        }
    }
}

sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    // This relation represents the calculated level of access the User has to
    // each Object, which may change over the course of a simulation.
    var calculated: Permission one -> set Object,
}

fact calculate_user_permissions {
    always {
        all u: User, o: Object {
            // A user's calculated Permission to an Object is the greatest Permission to that Object
            // across all its Groups.
            ~(u.calculated)[o] = ordering/max[~(u.groups.calculated)[o] + CannotSee]
        }
    }
}

// Describing all of the transitions that occur during a simulation
// https://haslab.github.io/formal-software-design/modelling-tips/index.html#an-idiom-to-depict-events

enum Event { Stutter, Move }

// A stutter is a transition where nothing changes
pred stutter {
    parent' = parent
}

fun stutter_happens : set Event {
    { e: Stutter | stutter }
}

// True iff `user` moved `src` into `dst`
pred move[user: User, src: Object, dst: Folder] {
    // Can't move something into itself or one of its children
    src not in dst.*parent

    // Can't move something into the folder it's already in
    src not in dst.children

    // User must own both the source and destination
    src in user.calculated[Own]
    dst in user.calculated[Own]

    // The source object's parent changes to dst, everything else is the same
    parent' = parent - src->src.parent + src->dst
}

fun move_happens : set Event -> set User -> set Object -> one Folder {
    { e: Move, u: User, src: Object, dst: Folder | move[u, src, dst] }
}

fun events : set Event {
    stutter_happens + move_happens.Folder.Object.User
}

fact traces {
    always some events
}

run move_an_object {
    some u: User, src: Object, dst: Folder | move[u, src, dst]
}

run inherited_permission {
    some g: Group, o: Object {
        o not in g.explicit[Own]
        o not in g.calculated[Own]
        eventually o in g.calculated[Own]
    }
} for 1 User, 2 Group, 3 Object

check maintains_tree_structure {
    always graph/treeRootedAt[children, RootFolder]
}

check calculated_permission_correctness {
    all g: Group, p: Permission, o: g.explicit[p] {
        ordering/gte[~(g.calculated)[o], p]
    }
}

// True iff a user changed their own permissions by moving something
pred user_changes_own_permissions {
    some u: User, src: Object, dst: Folder {
        move[u, src, dst]
        u.calculated != u.calculated'
    }
}

// Verify that users can't change their own level of access
check user_cannot_change_own_permissions {
    not user_changes_own_permissions
} for 2 User, 4 Group, 4 Object, 2 steps
