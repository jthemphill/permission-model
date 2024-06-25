abstract sig Object {}

sig App extends Object {}

sig Folder extends Object {
    // Folders can contain Apps and other Folders
    children: set Object,
}

// You should be able to execute this and see a picture of a filesystem!
run make_filesystem {
} for exactly 2 Folder, exactly 1 App
