use mork::space::Space;

#[test]
fn json_to_paths_round_trips_owned_streamed_paths() {
    let json = br#"{
        "name": "Ada",
        "active": true,
        "scores": [1, 2],
        "empty": {}
    }"#;

    let mut encoded = Vec::new();
    let mut source = Space::new();
    let written = source.json_to_paths(json, &mut encoded).unwrap();
    assert!(written > 0);

    let mut restored = Space::new();
    pathmap::paths_serialization::deserialize_paths(
        restored.btm.write_zipper(),
        std::io::Cursor::new(&encoded),
        (),
    )
    .unwrap();

    let mut output = Vec::new();
    restored.dump_all_sexpr(&mut output).unwrap();
    let output = String::from_utf8(output).unwrap();

    assert!(output.contains("(name Ada)"), "{output}");
    assert!(output.contains("(active true)"), "{output}");
    assert!(output.contains("(scores (0 1))"), "{output}");
    assert!(output.contains("(scores (1 2))"), "{output}");
}

#[test]
fn singular_json_path_value_pattern_queries_loaded_json() {
    let json = br#"{
        "profile": {
            "name": "Ada",
            "scores": [1, 2],
            "tags": ["engineer", "math"]
        },
        "active": true
    }"#;

    let mut space = Space::new();
    assert_eq!(space.load_json(json).unwrap(), 6);

    let generated = space
        .singular_json_path_value_pattern("$.profile.scores[1]")
        .unwrap();
    let expected = mork::expr!(space, "[2] profile [2] scores [2] 1 $");
    assert_eq!(
        generated,
        unsafe { expected.span().as_ref().unwrap() }.to_vec()
    );

    let product_pattern = mork::expr!(space, "[2] , [2] profile [2] scores [2] 1 $");
    let product_count = Space::query_multi(&space.btm, product_pattern, |_, _| true);

    assert_eq!(product_count, 1);
}
