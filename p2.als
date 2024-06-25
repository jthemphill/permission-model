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
// The lowest permission in Retool is "None", but `none` is a reserved keyword
// in Alloy. I'm going to use the term `CannotSee` throughout this spec instead.
// Declaring an enum automatically imports the ordering module.
enum Permission { CannotSee, Use, Edit, Own }

sig Group {
    // A Group has 0 or 1 explicitly granted permissions to each Object
    // Not using the `var` keyword because this shouldn't change over the course
    // of a simulation
    explicit: Permission lone -> set Object,
    // These result in calculated permissions which *do* change over the course of a simulation.
    var calculated: Permission one -> set Object,
}

fact calculate_group_permissions {
    always {
        all g: Group, p: Permission, o: Object {
            // A Group's calculated permission to the object is the first explicit permission we find
            // as we go up the tree
            o in g.calculated[p] iff {
                some ancestor: o.*parent {
                    ancestor in g.explicit[p]
                    no closer_ancestor: o.*parent & ancestor.^children {
                        closer_ancestor in g.explicit[Permission]
                    }
                }
            }
        }
    }
}

// For now, we use only one User.
one sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    // This relation represents the calculated level of access the User has to
    // each Object.
    var calculated: Permission one -> set Object,
}

fact calculate_user_permissions {
    always {
        all o: Object {
            // A user's calculated Permission to an Object is the greatest Permission to that Object
            // across all its Groups.
            //
            // We are using `max` from the ordering module, which was automatically imported because
            // Permission is an enum.
            ~(User.calculated)[o] = ordering/max[{ p: Permission | o in User.groups.calculated[p] } + { CannotSee }]
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

pred move[src: Object, dst: Folder] {
    // Can't move something into itself or one of its children
    src not in dst.*parent

    // Not actually moving it if you're already in the destination folder
    dst not in src.parent

    // User must own both the source and destination
    src in User.calculated[Own]
    dst in User.calculated[Own]

    // Change the source's parent
    parent' = parent - src->src.parent + src->dst
}

fun move_happens : set Event -> set Object one -> one Folder {
    { e: Move, src: Object, dst: Folder | move[src, dst] }
}

fun events : set Event {
    stutter_happens + move_happens.Object.Folder
}

fact traces {
    always some events
}

run move_an_object {
    some src: Object, dst: Folder | eventually move[src, dst]
}

run inherited_permission {
    some g: Group, o: Object {
        o not in g.explicit[Own]
        not o in g.calculated[Own]
        eventually o in g.calculated[Own]
    }
} for 2 Group, 3 Object

check maintains_tree_structure {
    always graph/treeRootedAt[children, RootFolder]
}

check calculated_permission_correctness {
    all g: Group, o: Object, p: Permission {
        o in g.explicit[p] implies o in g.calculated[p]
    }
}

run user_self_grants_own_access {
    some o: Object {
        o in User.calculated[CannotSee]
        eventually o in User.calculated[Own]
    }
} for 2 Group, 4 Object, 2 steps

// True iff you can't set a lower permission for a child than its parents have
pred children_have_greater_perms_than_parent {
    all g: Group, o: Object, p: Permission {
        o in g.explicit[p] implies {
            no greater_perm: ordering/nexts[p] {
                some o.^parent & g.explicit[greater_perm]
            }
        }
    }
}

// Verify that if children have greater permissions than their parents at the beginning, moving
// things around can't change that
check children_always_have_greater_perms_than_parent {
    children_have_greater_perms_than_parent implies always children_have_greater_perms_than_parent
}

// Verify that users can't change their own level of access if we enforce that children must have
// greater permissions than their parents at the beginning
check user_cannot_gain_or_lose_access_if_children_have_greater_explicit_perms_than_parents {
    children_have_greater_perms_than_parent implies User.calculated = User.calculated'
}
