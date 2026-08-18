#![feature(gen_blocks)]
#![feature(coroutine_trait)]
#![feature(coroutines)]
#![feature(stmt_expr_attributes)]
#![feature(more_float_constants)]

pub mod space;
/// The worst-case-optimal leapfrog join. Compiled only under the `leapfrog` feature, which is
/// also what routes conjunctive bodies to it; without the feature the engine is unchanged.
#[cfg(feature = "leapfrog")]
pub mod leapfrog;
mod sources;
mod sinks;
mod pure;

pub use sinks::WriteResourceRequest;
pub use sources::ResourceRequest;

#[cfg(test)]
mod tests {
    use super::space::Space;

    #[test]
    fn count_sink_variable_template_uses_write_root_relative_path() {
        let mut s = Space::new();

        s.add_all_sexpr(
            br#"
(foo 1) (foo 2) (foo 3)
(exec 0 (, (foo $x)) (O (count (tag $q) $ (cux $x))))
(exec 1 (, (foo $x)) (O (count (fixed $q) 3 (cux $x))))
            "#,
        ).unwrap();

        s.metta_calculus(1000000000000000);

        let mut output = vec![];
        s.dump_all_sexpr(&mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("(tag $a)\n"), "output was {output:?}");
        assert!(!output.contains("(tag (tag $a))\n"), "output was {output:?}");
        assert!(output.contains("(fixed $a)\n"), "output was {output:?}");
        assert!(!output.contains("(fixed (fixed $a))\n"), "output was {output:?}");
    }

    #[test]
    fn count_sink_constant_template_uses_only_template_prefix() {
        let mut s = Space::new();

        s.add_all_sexpr(
            br#"
(foo 1) (foo 2) (foo 3)
(exec 0 (, (foo $x)) (O (count (tag constant) $ (cux $x))))
            "#,
        ).unwrap();

        s.metta_calculus(1000000000000000);

        let mut output = vec![];
        s.dump_all_sexpr(&mut output).unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "(foo 1)\n(foo 2)\n(foo 3)\n(tag constant)\n");

        let expected = crate::expr!(s, "[2] tag constant");
        let expected = unsafe { expected.span().as_ref().unwrap() };
        let paths: Vec<Vec<u8>> = s.btm.iter().map(|(p, _)| p.to_vec()).collect();
        assert!(paths.iter().any(|p| p == expected));
        assert!(!paths.iter().any(|p| p.starts_with(expected) && p.len() > expected.len()));
    }

    #[test]
    fn reduction_sinks_keep_variable_template_paths_root_relative() {
        for sink in [
            "(count (tag $q) $ (cux $x))",
            "(hash (tag $q) $ (cux $x))",
            "(and (tag $q) $ (cux $x))",
            "(sum (tag $q) $ $x)",
            "(fmin (tag $q) $ $x)",
        ] {
            let mut s = Space::new();
            let input = format!(
                "(foo 1) (foo 2) (foo 3)\n(exec 0 (, (foo $x)) (O {sink}))"
            );
            s.add_all_sexpr(input.as_bytes()).unwrap();
            s.metta_calculus(1000000000000000);

            let expected = crate::expr!(s, "[2] tag $");
            let expected = unsafe { expected.span().as_ref().unwrap() };
            let paths: Vec<Vec<u8>> = s.btm.iter().map(|(p, _)| p.to_vec()).collect();
            assert!(paths.iter().any(|p| p == expected), "sink {sink} output {paths:?}");
            assert!(!paths.iter().any(|p| p.starts_with(expected) && p.len() > expected.len()),
                    "sink {sink} output {paths:?}");
        }

        for sink in [
            "(count (tag $q) $ (cux $x))",
            "(hash (tag $q) $ (cux $x))",
            "(and (tag $q) $ (cux $x))",
            "(sum (tag $q) $ $x)",
            "(fmin (tag $q) $ $x)",
        ] {
            let mut s = Space::new();
            let sink = sink.replace("(tag $q)", "(tag constant)");
            let input = format!(
                "(foo 1) (foo 2) (foo 3)\n(exec 0 (, (foo $x)) (O {sink}))"
            );
            s.add_all_sexpr(input.as_bytes()).unwrap();
            s.metta_calculus(1000000000000000);

            let expected = crate::expr!(s, "[2] tag constant");
            let expected = unsafe { expected.span().as_ref().unwrap() };
            let paths: Vec<Vec<u8>> = s.btm.iter().map(|(p, _)| p.to_vec()).collect();
            assert!(paths.iter().any(|p| p == expected), "sink {sink} output {paths:?}");
            assert!(!paths.iter().any(|p| p.starts_with(expected) && p.len() > expected.len()),
                    "sink {sink} output {paths:?}");
        }
    }
}
