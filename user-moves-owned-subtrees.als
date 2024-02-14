/**
 * Model representing a permissions-based filesystem.
 *
 * It has these facts, which are true today:
 *
 * 1. There are pages and folders arranged in a tree.
 * 2. A User can have many Groups, and a Group can have many Users.
 * 3. There are four Permissions, in decreasing order of strength:
 *    Own, Edit, Use, and None.
 * 4. A User's level of access for an Object is the max of the Permissions
 *    held by each of the User's Groups for that Object.
 * 5. A Group's level of access to an Object is the Permission it was
 *    explicitly granted, either to that object or to its nearest ancestor
 *    with an explicit grant.
 * 6. A User can move any Page that they Own.
 *
 * And we are thinking of adding this fact:
 *
 * 7. A user can also move any Folder that they Own.
 *
 * There's a property that I think is pretty important in a permissions system:
 *
 * 1. If a user does not have access to an object, they can never give
 *    themselves access to the object just by moving objects around.
 *
 * This spec shows that this property **no longer** holds when we give users
 * the ability to move Folders.
 */

open util/ordering[Permission]

// There is always exactly one RootFolder
one sig RootFolder {
}

// Each Object has a parent Folder
abstract sig Object {
    var parent: one (Folder + RootFolder)
}

// There are two kinds of Object: Page and Folder
sig Page, Folder extends Object {
}

fact all_objects_connected_to_tree {
    always {
        all object: Object {
            RootFolder in object.*parent
        }
    }
}

fact tree_is_acyclic {
    always {
        no folder: Folder {
            folder in folder.^parent
        }
    }
}

/**
 * If you own an object, you can edit it. If you can edit it, you can use it.
 */
enum Permission { None, Use, Edit, Own }

// For now, we use only one User. Maybe we can have more, but I'm not sure what
// properties we care about when multiple users are involved.
one sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    var implicit: Permission -> Object,
} {
    always {
        all perm: Permission, object: Object |
           user_implicit[perm, object] <=> object in implicit[perm]
    }
}

sig Group {
    // The Objects this Group was explicitly granted permissions for
    explicit: Permission -> Object,
} {
    // You can only specify one setting for a Group/Object combination
    disj [explicit[Own], explicit[Edit], explicit[Use], explicit[None]]
}

/**
 * True if `group` implicitly grants `needed_perm` to `object`, based on the
 * directory structure of `object`.
 */
pred group_implicit[needed_perm: Permission, group: Group, object: Object] {
    some group_perm: Permission, ancestor_folder: object.*parent | {
        // True if the group has explicit permission for some ancestor folder
        ancestor_folder in group.explicit[group_perm]
        // and this permission is at least as strong as the permission we need
        gte[group_perm, needed_perm]
        // And also there is no middle folder, in between us and that ancestor,
        // which has a weaker explicit permission
        no
            middle_folder: (object.*parent - ancestor_folder.*parent),
            weaker_perm: Permission
        {
            lt[weaker_perm, needed_perm]
            middle_folder in group.explicit[weaker_perm]
        }
    }
}

pred user_implicit[needed_perm: Permission, object: Object] {
    // A user has implicit permission on an object if any of its groups have
    // that implicit permission
    some group: User.groups | group_implicit[needed_perm, group, object]
}

pred move_object[
    source_object: Object,
    target_folder: Folder + RootFolder
] {
    // User must own the source object
    user_implicit[Own, source_object]
    // User must own the target folder
    user_implicit[Own, target_folder]
    // User must also own all of the source object's children
    // all child_object: Object |
    //     (source_object in child_object.*parent) =>
    //         user_implicit[Own, child_object]
    // Object must not be a parent of the folder you're moving it into
    not source_object in target_folder.*parent
    // Object's parent becomes the target folder
    source_object.parent' = target_folder
    // All other parents stay unchanged
    all object: Object - source_object | object.parent' = object.parent
}

fact users_can_move_objects {
    always {
        one
            source_object: Object,
            target_folder: Folder + RootFolder
        | move_object[source_object, target_folder]
    }
}

run example_system {
} for 3 Object, 2 Group, 2 steps

/**
 * True if a user never gains access to an app
 */
check user_cannot_gain_access {
    all missing_perm: Permission, inaccessible_object: Object |
        not user_implicit[missing_perm, inaccessible_object] =>
            always not user_implicit[missing_perm, inaccessible_object]
} for 3 Object, 2 Group, 2 steps

/**
 * True if the user never gains or loses access to an app
 */
pred user_cannot_gain_or_lose_access {
    all missing_perm: Permission, inaccessible_object: Object |
        user_implicit[missing_perm, inaccessible_object] <=>
            always user_implicit[missing_perm, inaccessible_object]
}

check user_cannot_gain_or_lose_access {
    user_cannot_gain_or_lose_access
} for 3 Object, 2 Group, 2 steps

check user_cannot_gain_or_lose_access_if_only_one_group {
    user_cannot_gain_or_lose_access
} for 3 Object, 1 Group, 2 steps

/**
 * True if a folder never has a parent other than the root.
 */
pred subfolders_not_shipped {
    always {
        all object: Folder | object.parent = RootFolder
    }
}

check user_cannot_gain_or_lose_access_without_subfolders {
    subfolders_not_shipped => user_cannot_gain_or_lose_access
} for 3 Object, 2 Group, 2 steps


/**
 * True if a subfolder always has greater explicit permissions than its parents
 */
pred children_have_greater_perms_than_parent {
    all
        group: Group,
        child_perm: Permission,
        child: group.explicit[child_perm],
        ancestor: child.^parent - RootFolder |
            some ancestor_perm: Permission | {
                ancestor in group.explicit[ancestor_perm]
                ancestor_perm in child_perm + prevs[child_perm]
            }
}

check explicit_greater_implies_implicit_greater {
    children_have_greater_perms_than_parent =>
        all perm: Permission, child: Object, ancestor: child.^parent - RootFolder |
            user_implicit[perm, ancestor] => user_implicit[perm, child]
} for 3 Object, 2 Group, 1 steps

run children_have_greater_perms_than_parent for 3 Object, 2 Group, 2 steps

check user_cannot_gain_or_lose_access_if_children_have_greater_explicit_perms_than_parents {
    children_have_greater_perms_than_parent => user_cannot_gain_or_lose_access
} for 3 Object, 2 Group, 2 steps
