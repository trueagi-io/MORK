//! Conversions that never construct an in-memory Space.
use mork_expr::{Tag, item_byte};
use pathmap::paths_serialization::serialize_paths_from_funcs;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// Publish only a complete file; leave an existing destination intact on error.
struct Output {
    path: PathBuf,
    file: File,
}
impl Output {
    fn new(destination: &Path) -> io::Result<Self> {
        let parent = destination
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        loop {
            let path = parent.join(format!(
                ".mork-convert-{}-{}",
                std::process::id(),
                NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
            ));
            match OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(file) => return Ok(Self { path, file }),
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e),
            }
        }
    }
    fn publish(self, destination: &Path) -> io::Result<()> {
        fs::rename(&self.path, destination)
    }
}
impl Drop for Output {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

/// Iterative parser: one expression, one token and at most 64 variable names.
/// Symbols use the same inline encoding (including 63-byte truncation) as
/// ParDataParser. Quoted symbols retain their quotes and escape bytes.
struct Mm2Reader<R> {
    source: R,
    path: Vec<u8>,
    token: Vec<u8>,
    variables: Vec<Vec<u8>>,
    stack: Vec<(usize, u8)>,
    offset: u64,
}
impl<R: BufRead> Mm2Reader<R> {
    fn new(source: R) -> Self {
        Self {
            source,
            path: vec![],
            token: vec![],
            variables: vec![],
            stack: vec![],
            offset: 0,
        }
    }
    fn peek(&mut self) -> io::Result<Option<u8>> {
        Ok(self.source.fill_buf()?.first().copied())
    }
    fn take(&mut self) -> io::Result<Option<u8>> {
        let byte = self.peek()?;
        if byte.is_some() {
            self.source.consume(1);
            self.offset += 1;
        }
        Ok(byte)
    }
    fn error(&self, message: &str) -> io::Error {
        invalid(format!("mm2 byte {}: {message}", self.offset))
    }
    fn advance(&mut self) -> io::Result<bool> {
        self.path.clear();
        self.variables.clear();
        loop {
            let Some(c) = self.peek()? else {
                return if self.stack.is_empty() {
                    Ok(false)
                } else {
                    Err(self.error("unclosed expression"))
                };
            };
            if c.is_ascii_whitespace() {
                self.take()?;
                continue;
            }
            if c == b';' {
                while let Some(b) = self.take()? {
                    if b == b'\n' {
                        break;
                    }
                }
                continue;
            }
            if c == b')' {
                self.take()?;
                let Some((position, arity)) = self.stack.pop() else {
                    return Err(self.error("unexpected ')'"));
                };
                self.path[position] = item_byte(Tag::Arity(arity));
                if self.stack.is_empty() {
                    return Ok(true);
                }
                continue;
            }
            if let Some((_, arity)) = self.stack.last_mut() {
                if *arity == 63 {
                    return Err(self.error("more than 63 children"));
                }
                *arity += 1;
            }
            if c == b'(' {
                self.take()?;
                self.stack.push((self.path.len(), 0));
                self.path.push(0);
                continue;
            }
            self.token.clear();
            if c == b'"' {
                self.take()?;
                self.token.push(c);
                loop {
                    let b = self
                        .take()?
                        .ok_or_else(|| self.error("unclosed quoted symbol"))?;
                    self.token.push(b);
                    if b == b'"' {
                        break;
                    }
                    if b == b'\\' {
                        let escaped = self
                            .take()?
                            .ok_or_else(|| self.error("unfinished escape"))?;
                        self.token.push(escaped);
                    }
                }
            } else {
                while let Some(b) = self.peek()? {
                    if b.is_ascii_whitespace() || b == b'(' || b == b')' {
                        break;
                    }
                    self.token.push(b);
                    self.take()?;
                }
            }
            if c == b'$' {
                if let Some(index) = self.variables.iter().position(|v| v == &self.token) {
                    self.path.push(item_byte(Tag::VarRef(index as u8)));
                } else {
                    if self.variables.len() == 64 {
                        return Err(self.error("more than 64 variables"));
                    }
                    self.variables.push(self.token.clone());
                    self.path.push(item_byte(Tag::NewVar));
                }
            } else {
                let len = self.token.len().min(63);
                self.path.push(item_byte(Tag::SymbolSize(len as u8)));
                self.path.extend_from_slice(&self.token[..len]);
            }
            if self.path.len() > u32::MAX as usize {
                return Err(self.error("expression exceeds .paths length limit"));
            }
            if self.stack.is_empty() {
                return Ok(true);
            }
        }
    }
}

/// `.upaths` has precisely PathMap's zlib-compressed, length-prefixed `.paths`
/// representation, retaining input order and duplicates. Memory is O(max atom).
pub fn mm2_to_upaths(input: &Path, output: &Path) -> io::Result<usize> {
    if cfg!(feature = "interning") {
        return Err(invalid(
            "streaming mm2 conversion requires inline symbols; rebuild without interning",
        ));
    }
    let mut source = Mm2Reader::new(BufReader::with_capacity(256 * 1024, File::open(input)?));
    let target = Output::new(output)?;
    let stats = {
        let mut writer = BufWriter::with_capacity(256 * 1024, &target.file);
        let stats = serialize_paths_from_funcs(
            &mut writer,
            &mut source,
            |s| s.advance(),
            |s| Some(&s.path),
        )?;
        writer.flush()?;
        stats
    };
    target.publish(output)?;
    Ok(stats.path_count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::{ParDataParser, Space};
    use mork_expr::{Expr, ExprZipper};
    use mork_frontend::bytestring_parser::{Context, Parser};

    #[test]
    #[cfg(not(feature = "interning"))]
    fn streaming_parser_matches_existing_parser() {
        let input = b"; comment\n(foo (bar $x) $x $y \"a \\\" b\") () $v $v abc (a b)";
        let space = Space::new();
        let mut parser = ParDataParser::new(&space.sm);
        let mut context = Context::new(input);
        let mut stream = Mm2Reader::new(BufReader::with_capacity(1, &input[..]));
        while stream.advance().unwrap() {
            let mut buffer = [0; 1024];
            let mut zipper = ExprZipper::new(Expr {
                ptr: buffer.as_mut_ptr(),
            });
            parser.sexpr(&mut context, &mut zipper).unwrap();
            assert_eq!(stream.path, buffer[..zipper.loc]);
            context.variables.clear();
        }
    }

    #[test]
    #[cfg(not(feature = "interning"))]
    fn upaths_round_trip_and_failed_conversion_preserves_destination() {
        let mut input = Output::new(&std::env::temp_dir().join("input.mm2")).unwrap();
        input.file.write_all(b"(z $v $v) (a) (z $v $v)").unwrap();
        let output = Output::new(&std::env::temp_dir().join("output.upaths")).unwrap();
        assert_eq!(mm2_to_upaths(&input.path, &output.path).unwrap(), 3);
        let mut paths = Vec::new();
        pathmap::paths_serialization::for_each_deserialized_path(
            File::open(&output.path).unwrap(),
            |_, p| {
                paths.push(p.to_vec());
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(paths.len(), 3);
        assert_eq!(paths[0], paths[2]);
        assert!(paths[0] > paths[1]);
        let before = fs::read(&output.path).unwrap();
        fs::write(&input.path, b"(broken").unwrap();
        assert!(mm2_to_upaths(&input.path, &output.path).is_err());
        assert_eq!(fs::read(&output.path).unwrap(), before);
    }

    #[test]
    fn streaming_parser_boundaries_and_errors() {
        let input = b"(a ; comment\r\n b)\r\n\"a\n(b)\"";
        let mut reader = Mm2Reader::new(BufReader::with_capacity(1, &input[..]));
        assert!(reader.advance().unwrap());
        assert_eq!(reader.path, [2, 193, b'a', 193, b'b']);
        assert!(reader.advance().unwrap());
        assert!(!reader.advance().unwrap());
        for bad in ["(", ")", "\"oops", "(a", "\"escape\\"] {
            assert!(Mm2Reader::new(bad.as_bytes()).advance().is_err(), "{bad}");
        }
        let deep = format!("{}a{}", "(".repeat(10000), ")".repeat(10000));
        assert!(Mm2Reader::new(deep.as_bytes()).advance().unwrap());
        let wide = format!("({})", "a ".repeat(64));
        assert!(Mm2Reader::new(wide.as_bytes()).advance().is_err());
    }
}
