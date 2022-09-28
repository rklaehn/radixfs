# RadixFS

A toy file system based on https://github.com/cloudpeers/radixdb, modified from the simple file system example in fuser: https://github.com/cberner/fuser/blob/master/examples/simple.rs

Usage:

```
mkdir mnt
cargo run -- --mount-point mnt
```

In another window, go into mnt and do the usual file system stuff.