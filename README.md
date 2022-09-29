# RadixFS

A toy file system based on https://github.com/cloudpeers/radixdb, modified from the simple file system example in fuser: https://github.com/cberner/fuser/blob/master/examples/simple.rs

Usage:

```
mkdir mnt
cargo run -- --mount-point mnt --block-file test.db
```

In another window, go into mnt and do the usual file system stuff.

```
cd mnt
touch test
echo foo > bar
...
```

Supports directories, files and symlinks, file attributes and xattrs.