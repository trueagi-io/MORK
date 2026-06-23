use mork::binding_env::{
    Binding, BindingEnv, BindingEnvError, BindingSnapshot, BindingSource, MAX_BINDING_SLOTS,
};
use mork::term_identity::{FactId, TermId};

fn term(id: u64) -> TermId {
    TermId(id)
}

#[test]
fn binding_env_provides_fixed_slot_scoped_rollback() {
    let mut env = BindingEnv::new();

    assert_eq!(MAX_BINDING_SLOTS, 64);
    assert!(env.is_empty());
    assert_eq!(env.bind_term(1, term(10)), Ok(true));
    assert_eq!(env.bind_term(1, term(10)), Ok(true));
    assert_eq!(env.trail_len(), 1);

    let mark = env.mark();
    assert_eq!(env.bind_term(2, term(20)), Ok(true));
    assert_eq!(
        env.bind(
            3,
            Binding {
                term: term(30),
                fact: Some(FactId(7)),
                source: BindingSource(42),
            },
        ),
        Ok(true)
    );
    assert_eq!(env.bind_term(2, term(21)), Ok(false));
    assert_eq!(env.get(2), Ok(Some(Binding::from_term(term(20)))));

    let snapshot: BindingSnapshot = env.capture();
    let scoped_len = env
        .with_rollback(|env| {
            assert_eq!(env.bind_term(4, term(40)), Ok(true));
            env.len()
        })
        .unwrap();

    assert_eq!(scoped_len, 4);
    assert_eq!(env.get(4), Ok(None));
    assert_eq!(env.len(), 3);
    assert_eq!(
        env.iter_bound()
            .map(|(slot, binding)| (slot, binding.term))
            .collect::<Vec<_>>(),
        vec![(1, term(10)), (2, term(20)), (3, term(30))]
    );

    assert_eq!(env.rollback_to(mark), Ok(()));
    assert_eq!(env.get(1), Ok(Some(Binding::from_term(term(10)))));
    assert_eq!(env.get(2), Ok(None));
    assert_eq!(env.get(3), Ok(None));

    env.restore(&snapshot);
    assert_eq!(env.trail_len(), 0);
    assert_eq!(env.len(), 3);
    assert_eq!(
        env.bind_term(64, term(64)),
        Err(BindingEnvError::SlotOutOfRange { slot: 64 })
    );
}
