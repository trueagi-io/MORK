use crate::*;

#[test]
fn example() {
  let handle = SharedMapping::new();
  
  core::assert_eq!(handle.get_sym(b"abc"), None);
  core::assert_eq!(handle.get_bytes(5), None);

  let permit = handle.try_aquire_permission().unwrap();

  let sym = permit.get_or_insert(b"abc");
  drop(permit);
  core::assert_eq!(Some(sym), handle.get_sym(b"abc"));
  core::assert_eq!(Some(&b"abc"[..]), handle.get_bytes(sym));
}