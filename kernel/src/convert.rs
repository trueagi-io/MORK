//! Conversions that never construct an in-memory Space.
use mork_expr::{Tag, item_byte};
use pathmap::paths_serialization::serialize_paths_from_funcs;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Read, Write};
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

// A checked zlib reader: unlike a permissive decompressor, EOF before
// StreamEnd, partial records, corrupt checksums and trailing data are errors.
struct ZlibReader<R> {
    source: R,
    codec: flate2::Decompress,
    finished: bool,
}
impl<R: BufRead> ZlibReader<R> {
    fn new(source: R) -> Self {
        Self {
            source,
            codec: flate2::Decompress::new(true),
            finished: false,
        }
    }
}
impl<R: BufRead> Read for ZlibReader<R> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        if output.is_empty() || self.finished {
            return Ok(0);
        }
        loop {
            let input = self.source.fill_buf()?;
            let before_in = self.codec.total_in();
            let before_out = self.codec.total_out();
            let status = self
                .codec
                .decompress(input, output, flate2::FlushDecompress::None)
                .map_err(|e| invalid(format!("invalid .paths zlib stream: {e}")))?;
            let consumed = (self.codec.total_in() - before_in) as usize;
            let produced = (self.codec.total_out() - before_out) as usize;
            self.source.consume(consumed);
            if status == flate2::Status::StreamEnd {
                if !self.source.fill_buf()?.is_empty() {
                    return Err(invalid("trailing bytes after .paths zlib stream"));
                }
                self.finished = true;
                return Ok(produced);
            }
            if produced > 0 {
                return Ok(produced);
            }
            if consumed == 0 {
                return Err(invalid("truncated .paths zlib stream"));
            }
        }
    }
}

struct Records<R> {
    source: R,
    path: Vec<u8>,
    max_path: usize,
}
impl<R: Read> Records<R> {
    fn new(source: R, max_path: usize) -> Self {
        Self {
            source,
            path: vec![],
            max_path,
        }
    }
    fn advance(&mut self) -> io::Result<bool> {
        let mut length = [0; 4];
        // read_exact handles Interrupted, including before the first byte.
        loop {
            match self.source.read(&mut length[..1]) {
                Ok(0) => return Ok(false),
                Ok(_) => break,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
        self.source.read_exact(&mut length[1..])?;
        let length = u32::from_le_bytes(length) as usize;
        if length > self.max_path {
            return Err(invalid(format!(
                "path length {length} exceeds memory-budget limit {}; increase --memory-mib",
                self.max_path
            )));
        }
        self.path.resize(length, 0);
        self.source.read_exact(&mut self.path)?;
        Ok(true)
    }
}

const IO_BUFFER: usize = 16 * 1024;
fn paths_reader(
    input: &Path,
    max_path: usize,
) -> io::Result<Records<BufReader<ZlibReader<BufReader<File>>>>> {
    Ok(Records::new(
        BufReader::with_capacity(
            IO_BUFFER,
            ZlibReader::new(BufReader::with_capacity(IO_BUFFER, File::open(input)?)),
        ),
        max_path,
    ))
}
fn write_record(writer: &mut impl Write, path: &[u8]) -> io::Result<()> {
    let length =
        u32::try_from(path.len()).map_err(|_| invalid("path exceeds .paths length limit"))?;
    writer.write_all(&length.to_le_bytes())?;
    writer.write_all(path)
}

struct Scratch(PathBuf);
impl Scratch {
    fn new(parent: &Path) -> io::Result<Self> {
        loop {
            let path = parent.join(format!(
                "mork-sort-{}-{}",
                std::process::id(),
                NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e),
            }
        }
    }
    fn run(&self) -> PathBuf {
        self.0
            .join(NEXT_TEMP.fetch_add(1, Ordering::Relaxed).to_string())
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Chunk {
    bytes: Vec<u8>,
    entries: Vec<(usize, usize)>,
    byte_limit: usize,
    entry_limit: usize,
}
impl Chunk {
    fn new(memory: usize) -> Self {
        let byte_limit = memory / 3;
        let entry_limit = memory / 6 / std::mem::size_of::<(usize, usize)>();
        Self {
            bytes: Vec::with_capacity(byte_limit),
            entries: Vec::with_capacity(entry_limit),
            byte_limit,
            entry_limit,
        }
    }
    fn fits(&self, path: &[u8]) -> bool {
        self.bytes.len() + path.len() <= self.byte_limit && self.entries.len() < self.entry_limit
    }
    fn push(&mut self, path: &[u8]) {
        self.entries.push((self.bytes.len(), path.len()));
        self.bytes.extend_from_slice(path);
    }
    fn spill(&mut self, scratch: &Scratch) -> io::Result<PathBuf> {
        let bytes = &self.bytes;
        self.entries
            .sort_unstable_by(|&(a, al), &(b, bl)| bytes[a..a + al].cmp(&bytes[b..b + bl]));
        let path = scratch.run();
        let mut writer = BufWriter::with_capacity(IO_BUFFER, File::create(&path)?);
        let mut previous: Option<&[u8]> = None;
        for &(start, len) in &self.entries {
            let value = &bytes[start..start + len];
            if previous != Some(value) {
                write_record(&mut writer, value)?;
            }
            previous = Some(value);
        }
        writer.flush()?;
        self.entries.clear();
        self.bytes.clear();
        Ok(path)
    }
}

/// Two-way merge keeps file descriptors and head buffers bounded, even for
/// arbitrarily many runs. Inputs are internally generated sorted unique runs.
fn merge_runs(
    left: &Path,
    right: &Path,
    scratch: &Scratch,
    max_path: usize,
) -> io::Result<PathBuf> {
    let mut a = Records::new(
        BufReader::with_capacity(IO_BUFFER, File::open(left)?),
        max_path,
    );
    let mut b = Records::new(
        BufReader::with_capacity(IO_BUFFER, File::open(right)?),
        max_path,
    );
    let output = scratch.run();
    let mut writer = BufWriter::with_capacity(IO_BUFFER, File::create(&output)?);
    let mut has_a = a.advance()?;
    let mut has_b = b.advance()?;
    while has_a || has_b {
        let order = match (has_a, has_b) {
            (true, true) => a.path.cmp(&b.path),
            (true, false) => std::cmp::Ordering::Less,
            _ => std::cmp::Ordering::Greater,
        };
        if order.is_le() {
            write_record(&mut writer, &a.path)?;
        } else {
            write_record(&mut writer, &b.path)?;
        }
        if order.is_le() {
            has_a = a.advance()?;
        }
        if order.is_ge() {
            has_b = b.advance()?;
        }
    }
    writer.flush()?;
    drop(a);
    drop(b);
    fs::remove_file(left)?;
    fs::remove_file(right)?;
    Ok(output)
}

// Binary carry merging stores at most one run per level, never an unbounded
// in-memory run list. Each record is merged O(log(number of initial runs)) times.
fn add_run(
    mut run: PathBuf,
    levels: &mut [Option<PathBuf>; 64],
    scratch: &Scratch,
    max_path: usize,
) -> io::Result<()> {
    for slot in levels {
        match slot.take() {
            None => {
                *slot = Some(run);
                return Ok(());
            }
            Some(other) => {
                run = merge_runs(&other, &run, scratch, max_path)?;
            }
        }
    }
    Err(invalid("too many sort runs"))
}

/// External bytewise sort with deduplication. The memory budget covers record
/// buffers and sort workspace; small codec/runtime allocations are additional.
/// Oversize records fail rather than silently exceeding the configured bound.
pub fn upaths_to_paths(
    input: &Path,
    output: &Path,
    memory: usize,
    temp_dir: &Path,
) -> io::Result<usize> {
    if memory < 1024 * 1024 {
        return Err(invalid("--memory-mib must be at least 1"));
    }
    let max_path = memory / 16;
    let scratch = Scratch::new(temp_dir)?;
    let mut source = paths_reader(input, max_path)?;
    let mut chunk = Chunk::new(memory);
    let mut levels = std::array::from_fn(|_| None);
    while source.advance()? {
        if !chunk.fits(&source.path) {
            add_run(chunk.spill(&scratch)?, &mut levels, &scratch, max_path)?;
        }
        chunk.push(&source.path);
    }
    if !chunk.entries.is_empty() {
        add_run(chunk.spill(&scratch)?, &mut levels, &scratch, max_path)?;
    }
    drop(chunk);
    drop(source);
    let mut final_run: Option<PathBuf> = None;
    for run in levels.into_iter().flatten() {
        final_run = Some(match final_run {
            None => run,
            Some(other) => merge_runs(&other, &run, &scratch, max_path)?,
        });
    }
    let target = Output::new(output)?;
    let stats = {
        let mut writer = BufWriter::with_capacity(IO_BUFFER, &target.file);
        // An empty input still needs a complete, valid empty zlib stream.
        let source: Box<dyn Read> = match final_run {
            Some(path) => Box::new(BufReader::with_capacity(IO_BUFFER, File::open(path)?)),
            None => Box::new(io::empty()),
        };
        let mut records = Records::new(source, max_path);
        let stats = serialize_paths_from_funcs(
            &mut writer,
            &mut records,
            |r| r.advance(),
            |r| Some(&r.path),
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

    fn write_paths(path: &Path, paths: &[Vec<u8>]) {
        let mut source = (0usize, paths);
        serialize_paths_from_funcs(
            &mut File::create(path).unwrap(),
            &mut source,
            |s| {
                s.0 += 1;
                Ok(s.0 <= s.1.len())
            },
            |s| Some(s.1[s.0 - 1].as_slice()),
        )
        .unwrap();
    }
    fn read_paths(path: &Path) -> Vec<Vec<u8>> {
        let mut source = paths_reader(path, 1 << 20).unwrap();
        let mut paths = vec![];
        while source.advance().unwrap() {
            paths.push(source.path.clone());
        }
        paths
    }

    #[test]
    fn external_sort_many_runs_matches_bytewise_set() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let input = scratch.0.join("input.upaths");
        let output = scratch.0.join("output.paths");
        let mut paths = vec![vec![], vec![0], vec![0, 0], vec![255], vec![]];
        for n in (0u32..35000).rev() {
            let mut path = n.to_be_bytes().to_vec();
            path.extend_from_slice(&[0, 255, 0]);
            path.extend(std::iter::repeat_n((n % 251) as u8, (n % 123) as usize));
            paths.push(path.clone());
            if n % 3 == 0 {
                paths.push(path);
            }
        }
        write_paths(&input, &paths);
        paths.sort();
        paths.dedup();
        assert_eq!(
            upaths_to_paths(&input, &output, 1 << 20, &scratch.0).unwrap(),
            paths.len()
        );
        assert_eq!(read_paths(&output), paths);
        // Compatibility with PathMap's independent streaming decoder.
        let mut index = 0;
        pathmap::paths_serialization::for_each_deserialized_path(
            File::open(&output).unwrap(),
            |_, path| {
                assert_eq!(path, paths[index]);
                index += 1;
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(index, paths.len());
        assert_eq!(fs::read_dir(&scratch.0).unwrap().count(), 2);
    }

    #[test]
    fn sort_empty_duplicates_and_corrupt_streams() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let input = scratch.0.join("input.upaths");
        let output = scratch.0.join("output.paths");
        for paths in [vec![], vec![vec![]; 3], vec![b"same".to_vec(); 25000]] {
            write_paths(&input, &paths);
            let mut expected = paths;
            expected.sort();
            expected.dedup();
            upaths_to_paths(&input, &output, 1 << 20, &scratch.0).unwrap();
            assert_eq!(read_paths(&output), expected);
        }
        write_paths(&input, &[vec![42; 2049], b"xyz".to_vec()]);
        let valid = fs::read(&input).unwrap();
        let before = fs::read(&output).unwrap();
        for len in 0..valid.len() {
            fs::write(&input, &valid[..len]).unwrap();
            assert!(
                upaths_to_paths(&input, &output, 1 << 20, &scratch.0).is_err(),
                "truncation {len}"
            );
            assert_eq!(fs::read(&output).unwrap(), before);
        }
        let mut bad = valid.clone();
        bad[valid.len() - 1] ^= 1;
        fs::write(&input, &bad).unwrap();
        assert!(upaths_to_paths(&input, &output, 1 << 20, &scratch.0).is_err());
        let mut bad = valid;
        bad.push(0);
        fs::write(&input, &bad).unwrap();
        assert!(upaths_to_paths(&input, &output, 1 << 20, &scratch.0).is_err());
        write_paths(&input, &[vec![0; (1 << 16) + 1]]);
        assert!(upaths_to_paths(&input, &output, 1 << 20, &scratch.0).is_err());
        // Valid compression, incomplete record header/payload.
        for raw in [vec![1], vec![2, 0, 0, 0, 42]] {
            let mut encoder = flate2::write::ZlibEncoder::new(
                File::create(&input).unwrap(),
                flate2::Compression::default(),
            );
            encoder.write_all(&raw).unwrap();
            encoder.finish().unwrap();
            assert!(upaths_to_paths(&input, &output, 1 << 20, &scratch.0).is_err());
        }
        assert_eq!(fs::read_dir(&scratch.0).unwrap().count(), 2);
    }

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
