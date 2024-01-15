/**
 * Model representing a permissions-based filesystem.
 *
 * It has these facts, which are true today:
 *
 * 1. There are pages and folders arranged in a tree.
 * 2. A User can have many Groups, and a Group can have many Users.
 * 3. There are four levels of access, in decreasing order of strength:
 *    Own, Edit, Use, and None.
 * 4. A user's level of access to an object is the max of their group's levels
 *    of access.
 * 5. A group's level of access to an object is the permission it was
 *    explicitly granted, either to that object or to its nearest ancestor
 *    with an explicit grant.
 * 6. A user can move any page that they Own.
 *
 * And we are thinking of adding this fact:
 *
 * 7. A user can also move any folder that they Own.
 *
 * There's a property that I think is pretty important in a permissions system:
 *
 * 1. If a user does not have access to an object, they can never give
 *    themselves access to the object just by moving objects around.
 *
 * This spec shows that this property **no longer** holds when we give users
 * the ability to move Folders.
 */

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

abstract sig Perm {
    includes: lone Perm
}

one sig Own, Edit, Use, None extends Perm {
}

fact permission_rankings {
    Own.includes = Edit
    Edit.includes = Use
    Use.includes = None
    None.includes = none
}

// For now, we use only one User. Maybe we can have more, but I'm not sure what
// properties we care about when multiple users are involved.
one sig User {
    // A User can be a member of multiple Groups
    groups: set Group,
    var implicit: Perm -> Object,
} {
    always {
        all perm: Perm, object: Object |
           user_implicit[perm, this, object] <=> object in implicit[perm]
    }
}

sig Group {
    // The Objects this Group was explicitly granted permissions for
    explicit: Perm -> Object,
} {
    // You can only specify one setting for a Group/Object combination
    disj [explicit[Own], explicit[Edit], explicit[Use], explicit[None]]
}

/**
 * True if `group` implicitly grants `needed_perm` to `object`, based on the
 * directory structure of `object`.
 */
pred group_implicit[needed_perm: Perm, group: Group, object: Object] {
    some group_perm: Perm, ancestor_folder: object.*parent | {
        // True if the group has explicit permission for some ancestor folder
        ancestor_folder in group.explicit[group_perm]
        // and this permission is at least as strong as the permission we need
        needed_perm in group_perm.*includes
        // And also there is no middle folder, in between us and that ancestor,
        // which has a weaker explicit permission
        no
            middle_folder: (object.*parent - ancestor_folder.*parent),
            weaker_perm: Perm
        {
            needed_perm not in weaker_perm.includes
            middle_folder in group.explicit[weaker_perm]
        }
    }
}

pred user_implicit[needed_perm: Perm, user: User, object: Object] {
    // A user has implicit permission on an object if any of its groups have
    // that implicit permission
    some group: user.groups | group_implicit[needed_perm, group, object]
}

pred move_object[
    user: User,
    source_object: Object,
    target_folder: Folder + RootFolder
] {
    // User must own the source object
    user_implicit[Own, user, source_object]
    // User must also own all of the source object's children
    all child_object: Object |
        (source_object in child_object.*parent) =>
            user_implicit[Own, user, child_object]
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
            user: User,
            source_object: Object,
            target_folder: Folder + RootFolder
        |
            move_object[user, source_object, target_folder]
    }
}

/**
 * True if a folder never has a parent other than the root.
 */
pred subfolders_not_shipped {
    always {
        all object: Folder | object.parent = RootFolder
    }
}

/**
 * True if a user never gains permissions on an app that an admin didn't grant
 * them.
 */
pred cannot_escalate {
    all missing_perm: Perm, escalating_user: User, inaccessible_object: Object |
        not user_implicit[missing_perm, escalating_user, inaccessible_object] =>
            always not user_implicit[missing_perm, escalating_user, inaccessible_object]
}

check {
    cannot_escalate
} for 3 Object, 2 Group, 3 steps

check {
    subfolders_not_shipped => cannot_escalate
} for 3 Object, 2 Group, 3 steps
