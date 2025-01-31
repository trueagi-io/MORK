//! this iterator has been coppied everywhere we needed it, at some point it would be nice to stop copy pasting it...

#[derive(Clone)]
pub(crate) struct CfIter {
    i: u8,
    w: u64,
    mask: [u64; 4]
}

impl CfIter {
    pub(crate) fn new(mask: &[u64; 4]) -> Self {
        Self {
            i: 0,
            w: mask[0],
            mask: *mask
        }
    }
}

impl Iterator for CfIter {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            if self.w != 0 {
                let wi = self.w.trailing_zeros() as u8;
                self.w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some(index)
            } else if self.i < 3 {
                self.i += 1;
                self.w = unsafe{ *self.mask.get_unchecked(self.i as usize) };
            } else {
                return None
            }
        }
    }
}
