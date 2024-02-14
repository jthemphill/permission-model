// File system objects
abstract sig FSObject { }
sig File, Dir extends FSObject { }

// A File System
sig FileSystem {
  var live: set FSObject,
  var root: Dir & live,
  var parent: (live - root) ->one (Dir & live),
  var contents: Dir -> FSObject
}{
  // live objects are reachable from the root
  live = root.*contents
  // parent is the inverse of contents
  parent = ~contents
}

// Move x to directory d
pred move [fs: FileSystem, x: FSObject, d: Dir] {
  (x + d) in fs.live
  d not in x.(fs.parent)
  fs.parent' = fs.parent - x->fs.parent[x] + x->d
}

// Delete the file or directory x
pred remove [fs: FileSystem, x: FSObject] {
  x in (fs.live - fs.root)
  fs.root' = fs.root
  fs.parent' = fs.parent - x->x.(fs.parent)
}

// Recursively delete the object x
pred removeAll [fs: FileSystem, x: FSObject] {
  x in (fs.live - fs.root)
  fs.root' = fs.root
  let subtree = x.*(fs.contents) |
      fs.parent' = fs.parent - subtree->(subtree.(fs.parent))
}

run move for 1 FileSystem, 4 FSObject
run remove for 1 FileSystem, 4 FSObject, 2 steps
run removeAll for 2 FileSystem, 4 FSObject

// Moving doesn't add or delete any file system objects
moveOkay: check {
  all fs: FileSystem, x: FSObject, d:Dir |
    move[fs, x, d] => fs'.live = fs.live
} for 5

// remove removes exactly the specified file or directory
removeOkay: check {
  all fs: FileSystem, x: FSObject |
    remove[fs, x] => fs.live' = fs.live - x
} for 5

// removeAll removes exactly the specified subtree
removeAllOkay: check {
  all fs: FileSystem, d: Dir |
    removeAll[fs, d] => fs.live' = fs.live - d.*(fs.contents)
} for 5 but exactly 1 FileSystem

// remove and removeAll has the same effects on files
removeAllSame: check {
  all fs1, fs2: FileSystem, f: File |
    fs1 = fs2 and remove[fs1, f] and removeAll[fs2, f] => fs1.live = fs2.live
} for 5
