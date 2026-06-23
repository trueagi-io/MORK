use crate::term_identity::{FactId, TermId};

/// The current MORK encoding uses six-bit variable references.
pub const MAX_BINDING_SLOTS: usize = 64;

/// Logical source of a binding row.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BindingSource(pub u32);

/// One fixed-slot binding entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Binding {
    /// Canonical term identity bound to the slot.
    pub term: TermId,
    /// Optional complete fact identity that supplied the term.
    pub fact: Option<FactId>,
    /// Source relation or snapshot cursor that produced the binding.
    pub source: BindingSource,
}

impl Binding {
    /// Constructs a binding from a canonical term alone.
    pub fn from_term(term: TermId) -> Self {
        Self {
            term,
            fact: None,
            source: BindingSource::default(),
        }
    }
}

impl Default for Binding {
    fn default() -> Self {
        Self::from_term(TermId(0))
    }
}

/// Rollback mark for [`BindingEnv`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BindingMark {
    trail_len: usize,
}

/// Captured binding state for explicit dynamic-environment restore.
#[derive(Clone, Debug)]
pub struct BindingSnapshot {
    slots: [Binding; MAX_BINDING_SLOTS],
    bound_mask: u64,
}

/// Error returned by fixed-slot binding operations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingEnvError {
    /// Slot index was outside the six-bit binding domain.
    SlotOutOfRange { slot: u8 },
    /// The mark was created from a different or later environment state.
    InvalidMark,
}

/// Fixed 64-slot binding environment with trail-based rollback.
#[derive(Clone, Debug)]
pub struct BindingEnv {
    slots: [Binding; MAX_BINDING_SLOTS],
    bound_mask: u64,
    trail: Vec<u8>,
}

fn masked_slots_equal(
    left: &[Binding; MAX_BINDING_SLOTS],
    right: &[Binding; MAX_BINDING_SLOTS],
    mut mask: u64,
) -> bool {
    while mask != 0 {
        let slot = mask.trailing_zeros() as usize;
        if left[slot] != right[slot] {
            return false;
        }
        mask &= mask - 1;
    }
    true
}

impl PartialEq for BindingSnapshot {
    fn eq(&self, other: &Self) -> bool {
        self.bound_mask == other.bound_mask
            && masked_slots_equal(&self.slots, &other.slots, self.bound_mask)
    }
}

impl Eq for BindingSnapshot {}

impl PartialEq for BindingEnv {
    fn eq(&self, other: &Self) -> bool {
        self.bound_mask == other.bound_mask
            && self.trail == other.trail
            && masked_slots_equal(&self.slots, &other.slots, self.bound_mask)
    }
}

impl Eq for BindingEnv {}

impl Default for BindingEnv {
    fn default() -> Self {
        Self {
            slots: [Binding::default(); MAX_BINDING_SLOTS],
            bound_mask: 0,
            trail: Vec::new(),
        }
    }
}

impl BindingEnv {
    /// Creates an empty binding environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the current rollback mark.
    pub fn mark(&self) -> BindingMark {
        BindingMark {
            trail_len: self.trail.len(),
        }
    }

    /// Captures the bound slots as an explicit dynamic environment.
    pub fn capture(&self) -> BindingSnapshot {
        BindingSnapshot {
            slots: self.slots,
            bound_mask: self.bound_mask,
        }
    }

    /// Restores a captured binding snapshot and clears the rollback trail.
    pub fn restore(&mut self, snapshot: &BindingSnapshot) {
        self.slots = snapshot.slots;
        self.bound_mask = snapshot.bound_mask;
        self.trail.clear();
    }

    /// Removes every binding.
    pub fn clear(&mut self) {
        self.bound_mask = 0;
        self.trail.clear();
    }

    /// Rolls back bindings introduced after `mark`.
    pub fn rollback_to(&mut self, mark: BindingMark) -> Result<(), BindingEnvError> {
        if mark.trail_len > self.trail.len() {
            return Err(BindingEnvError::InvalidMark);
        }

        while self.trail.len() > mark.trail_len {
            let Some(slot) = self.trail.pop() else {
                break;
            };
            self.bound_mask &= !(1_u64 << slot);
        }

        Ok(())
    }

    /// Runs `f` in a temporary binding extent and rolls back new bindings.
    ///
    /// Existing bindings remain visible to `f`; only bindings introduced after
    /// this method's entry mark are removed before returning. If the closure
    /// needs to report failure, return a `Result` as its own value.
    pub fn with_rollback<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> R,
    ) -> Result<R, BindingEnvError> {
        let mark = self.mark();
        let output = f(self);
        self.rollback_to(mark)?;
        Ok(output)
    }

    /// Binds `slot` to `binding`.
    ///
    /// Returns `Ok(true)` when the slot is newly bound or already carries the
    /// same term, and `Ok(false)` when a repeated variable conflicts.
    pub fn bind(&mut self, slot: u8, binding: Binding) -> Result<bool, BindingEnvError> {
        let index = Self::slot_index(slot)?;
        let bit = 1_u64 << slot;

        if self.bound_mask & bit == 0 {
            self.slots[index] = binding;
            self.bound_mask |= bit;
            self.trail.push(slot);
            return Ok(true);
        }

        Ok(self.slots[index].term == binding.term)
    }

    /// Binds `slot` to `term`.
    pub fn bind_term(&mut self, slot: u8, term: TermId) -> Result<bool, BindingEnvError> {
        self.bind(slot, Binding::from_term(term))
    }

    /// Returns the binding for `slot`, if present.
    pub fn get(&self, slot: u8) -> Result<Option<Binding>, BindingEnvError> {
        let index = Self::slot_index(slot)?;
        if self.bound_mask & (1_u64 << slot) != 0 {
            Ok(Some(self.slots[index]))
        } else {
            Ok(None)
        }
    }

    /// Returns true when `slot` currently has a binding.
    pub fn is_bound(&self, slot: u8) -> Result<bool, BindingEnvError> {
        Ok(self.bound_mask & (1_u64 << slot) != 0)
    }

    /// Bitmask of bound slots.
    pub fn bound_mask(&self) -> u64 {
        self.bound_mask
    }

    /// Number of currently bound slots.
    pub fn len(&self) -> usize {
        self.bound_mask.count_ones() as usize
    }

    /// Returns true when no slots are bound.
    pub fn is_empty(&self) -> bool {
        self.bound_mask == 0
    }

    /// Number of assignments tracked since the last clear or restore.
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// Iterates over bound slots in ascending slot order.
    pub fn iter_bound(&self) -> impl Iterator<Item = (u8, Binding)> + '_ {
        let mut mask = self.bound_mask;
        std::iter::from_fn(move || {
            if mask == 0 {
                return None;
            }
            let slot = mask.trailing_zeros() as u8;
            mask &= mask - 1;
            Some((slot, self.slots[usize::from(slot)]))
        })
    }

    fn slot_index(slot: u8) -> Result<usize, BindingEnvError> {
        if usize::from(slot) < MAX_BINDING_SLOTS {
            Ok(usize::from(slot))
        } else {
            Err(BindingEnvError::SlotOutOfRange { slot })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding(term: u64) -> Binding {
        Binding::from_term(TermId(term))
    }

    #[test]
    fn bind_reuses_existing_term_without_extending_trail() {
        let mut env = BindingEnv::new();

        assert_eq!(env.bind(3, binding(10)), Ok(true));
        assert_eq!(env.bind(3, binding(10)), Ok(true));
        assert_eq!(env.trail_len(), 1);
        assert_eq!(env.get(3), Ok(Some(binding(10))));
    }

    #[test]
    fn bind_reports_conflict_without_mutating_existing_binding() {
        let mut env = BindingEnv::new();

        assert_eq!(env.bind(3, binding(10)), Ok(true));
        assert_eq!(env.bind(3, binding(11)), Ok(false));
        assert_eq!(env.get(3), Ok(Some(binding(10))));
        assert_eq!(env.trail_len(), 1);
    }

    #[test]
    fn rollback_removes_bindings_after_mark() {
        let mut env = BindingEnv::new();
        env.bind(1, binding(10)).unwrap();
        let mark = env.mark();
        env.bind(2, binding(20)).unwrap();
        env.bind(3, binding(30)).unwrap();

        assert_eq!(env.rollback_to(mark), Ok(()));
        assert_eq!(env.get(1), Ok(Some(binding(10))));
        assert_eq!(env.get(2), Ok(None));
        assert_eq!(env.get(3), Ok(None));
        assert_eq!(env.bound_mask(), 0b10);
    }

    #[test]
    fn rollback_hides_stale_slot_until_it_is_rebound() {
        let mut env = BindingEnv::new();
        let mark = env.mark();
        env.bind(4, binding(40)).unwrap();

        env.rollback_to(mark).unwrap();
        assert_eq!(env.get(4), Ok(None));
        assert_eq!(env.bind(4, binding(41)), Ok(true));
        assert_eq!(env.get(4), Ok(Some(binding(41))));
    }

    #[test]
    fn capture_and_restore_replace_the_dynamic_environment() {
        let mut env = BindingEnv::new();
        env.bind(1, binding(10)).unwrap();
        let snapshot = env.capture();
        env.bind(2, binding(20)).unwrap();

        env.restore(&snapshot);

        assert_eq!(env.get(1), Ok(Some(binding(10))));
        assert_eq!(env.get(2), Ok(None));
        assert_eq!(env.trail_len(), 0);
    }

    #[test]
    fn clear_hides_bindings_without_preventing_reuse() {
        let mut env = BindingEnv::new();
        env.bind(1, binding(10)).unwrap();
        env.bind(2, binding(20)).unwrap();

        env.clear();
        assert!(env.is_empty());
        assert_eq!(env.get(1), Ok(None));
        assert_eq!(env.get(2), Ok(None));
        assert_eq!(env.trail_len(), 0);

        assert_eq!(env.bind(1, binding(11)), Ok(true));
        assert_eq!(env.get(1), Ok(Some(binding(11))));
    }

    #[test]
    fn equality_ignores_stale_unbound_slots() {
        let mut with_stale_slot = BindingEnv::new();
        with_stale_slot.bind(1, binding(10)).unwrap();
        with_stale_slot.clear();
        with_stale_slot.bind(2, binding(20)).unwrap();

        let mut direct = BindingEnv::new();
        direct.bind(2, binding(20)).unwrap();

        assert_eq!(with_stale_slot, direct);
    }

    #[test]
    fn snapshot_equality_ignores_stale_unbound_slots() {
        let mut with_stale_slot = BindingEnv::new();
        with_stale_slot.bind(1, binding(10)).unwrap();
        with_stale_slot.clear();

        assert_eq!(with_stale_slot.capture(), BindingEnv::new().capture());
    }

    #[test]
    fn iter_bound_visits_bound_slots_in_mask_order() {
        let mut env = BindingEnv::new();
        env.bind(5, binding(50)).unwrap();
        env.bind(1, binding(10)).unwrap();
        env.bind(3, binding(30)).unwrap();

        let slots = env.iter_bound().collect::<Vec<_>>();

        assert_eq!(
            slots,
            vec![(1, binding(10)), (3, binding(30)), (5, binding(50))]
        );
    }

    #[test]
    fn with_rollback_removes_only_extent_bindings() {
        let mut env = BindingEnv::new();
        env.bind(1, binding(10)).unwrap();

        let bound_count = env
            .with_rollback(|env| {
                assert_eq!(env.bind(2, binding(20)), Ok(true));
                assert_eq!(env.bind(1, binding(10)), Ok(true));
                env.len()
            })
            .unwrap();

        assert_eq!(bound_count, 2);
        assert_eq!(env.get(1), Ok(Some(binding(10))));
        assert_eq!(env.get(2), Ok(None));
        assert_eq!(env.trail_len(), 1);
    }

    #[test]
    fn with_rollback_restores_when_closure_returns_error_value() {
        let mut env = BindingEnv::new();

        let result = env
            .with_rollback(|env| {
                assert_eq!(env.bind(2, binding(20)), Ok(true));
                env.bind(64, binding(64))
            })
            .unwrap();

        assert_eq!(result, Err(BindingEnvError::SlotOutOfRange { slot: 64 }));
        assert_eq!(env.get(2), Ok(None));
        assert!(env.is_empty());
    }

    #[test]
    fn bind_rejects_slot_outside_six_bit_domain() {
        let mut env = BindingEnv::new();

        assert_eq!(
            env.bind(64, binding(10)),
            Err(BindingEnvError::SlotOutOfRange { slot: 64 })
        );
    }
}
