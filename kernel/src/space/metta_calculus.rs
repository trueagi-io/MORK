//! The Metta Calculus [`Machine`] is the state machine that allows running the Calculus
//! while being able to run outside logic and maintaing the internal consistancy on the Calculus state.


use std::{fmt::Debug, ops::ControlFlow};
type CF<B,C> = ControlFlow<B,C>;
use crate::space::*;

macro_rules! states {($( $STATE:ident $DOC:literal,)+) => {
        mod sealed {
            pub trait StateT {}
            use super::{Space, Controller, MachineHandle};
            #[allow(private_interfaces)]
            pub trait StateVal : StateT + Sized { const SELF : Self; fn handle_constructor<'machine, 'space, S:Space>(c : Controller<'machine, 'space, Self, S>)->MachineHandle<'machine, 'space, S>;}
        }
        use sealed::{StateT, StateVal};
        $(
        #[doc=$DOC]
        #[derive(Debug)]
        pub struct $STATE {}
        impl sealed::StateT for $STATE {}
        #[allow(private_interfaces)]
        impl StateVal       for $STATE { const SELF : Self = $STATE {}; fn handle_constructor<'machine, 'space, S:Space>(c : Controller<'machine, 'space, Self, S>)->MachineHandle<'machine, 'space, S> { MachineHandle::$STATE(c) }}
        )+
        /// [`MachineHandle`] takes an explicit [`Controller`] and turns it into a single type.
        pub enum MachineHandle<'machine, 'space, S : Space> {$(
            $STATE(Controller<'machine, 'space, $STATE, S>),
        )+}
    };
}

states!{
    LoopStart             "The machine is initialized to a valid state; \n\ncontinue to start iterating the loop.",
    PreTransform          "Run the transform",
}


/// The [`Machine`] holds the state of a metta_calculus process.
pub struct Machine<'space, 'auth, S: Space> {
    // /////////////
    // INIT ARGS //
    // ///////////
    space               : &'space S,
    auth                : &'auth S::Auth,

    // ////////////
    // INIT VARS //
    // ///////////
    prefix_len             : usize,
    /// once initialized, the buffer always starts with the bytes of the prefix.
    buffer                 : Vec<u8>,
    /// if an exec is defered, this flag is set. It is unset when a an exec suceeds to run.
    retry_remaining        : bool,
    /// the number successful transform iterations that will run
    steps_remaining        : usize,

    /// this is to protect your computer in debug from blowing your memory. It caused me an OS shutdown.
    #[cfg(debug_assertions)]
    hard_stop              : usize,

    // /////////////
    // LOOP VARS //
    // ///////////

    /// Holds the permission at the thread prefix, is taken out and reinserted when needed.
    exec_permission     : Option<<S as Space>::Writer<'space>>,
    /// This holds the patterns and templates until the current exec either succeeds or sucessfully defers.
    pattern_templates   : Option<(Vec<Expr>, Vec<Expr>)>,
}

/// Sometimes it is needed to aquire the permission fallibly, The MachineSpec makes it possible to separate that action, making following action infallible. 
pub struct MachineSpec<W /* W is always a Space::WritePermission, but forcing that can make the lifetimes not work out; so it is left to be infered at the call sight.*/> {
    exec_permission     : W ,
    prefix_len          : usize,
    buffer              : Vec<u8>,
    steps_remaining     : usize,
}

pub struct MachineSpecArgs<'space, 'auth, 'arg, S : Space> {
    pub space               : &'space S,
    pub thread_id_sexpr_str : &'arg str,
    pub steps               : usize,
    pub auth                : &'auth S::Auth
}

impl<'space, 'auth, 'arg, S : Space> MachineSpecArgs<'space, 'auth, 'arg, S> {
    /// Make the [`MachineSpec`]. This exits to aquire the exec prefix writer, without pinning the [`Machine`] until [`MachineSpec::init`] is called.
    /// This makes it possible to get the error earlier before dispating the [`Machine`].
    #[inline(always)]
    pub fn make(self) -> Result<MachineSpec<S::Writer<'space>>, S::PermissionErr> {
        let MachineSpecArgs { space, thread_id_sexpr_str, steps, auth } = self;

        // //GOAT, MM2-Syntax.  we need to lift these patterns out as constants so we can tweak the MM2 syntax without hunting through the implementation
        // //
        // // (exec (<location> $priority) $patterns $templates)
        let prefix_expr = space.sexpr_to_expr(&format!("(exec ({} $) $ $)", thread_id_sexpr_str)).unwrap();
        let prefix = unsafe { prefix_expr.borrow().prefix().unwrap().as_ref().unwrap() };

        Ok(MachineSpec {
            exec_permission : space.new_writer_retry(prefix, 1000, auth)?,
            prefix_len      : prefix.len(),
            buffer          : Vec::from(prefix),
            steps_remaining : steps
        })
    }
}


impl<'space, 'machine, S: Space> Machine<'space, 'machine, S> {
    /// an alternative contructor to make a [`MachineSpecArgs`].
    pub fn spec_args<'arg>( space : &'space S, thread_id_sexpr_str : &'arg str, steps : usize, auth : &'machine S::Auth ) -> MachineSpecArgs<'space, 'machine, 'arg, S> {
        MachineSpecArgs { space, thread_id_sexpr_str, steps, auth }
    }

    // The following methods are primarily here for inspection by users, without fear of breaking the integrity of the state machine.
    #[inline(always)] pub fn prefix         (&self) -> &[u8]             { &self.buffer[0..self.prefix_len]}
    /// on [`None`] the buffer only contains the prefix, on [`Some`] the last exec was found on lookup is output.
    #[inline(always)] pub fn current_exec   (&self) -> Option<&[u8]>     { (self.buffer.len() > self.prefix_len).then_some(&self.buffer[..]) }
    /// checks if at least one Deferal has be sheduled
    #[inline(always)] pub fn retry_remaining(&self) -> bool              { self.retry_remaining }
    #[inline(always)] pub fn space          (&self) -> &'space S         { self.space }
    #[inline(always)] pub fn auth           (&self) -> &'machine S::Auth { self.auth }

    #[inline(always)] pub fn buffer_invariant(&self) { core::debug_assert!(self.buffer.len()>=self.prefix_len); }
}

impl<'space, W> MachineSpec<W> {
    /// This sets the [`Machine`] in motion, from this point on the machine is effectively pinned.
    pub fn init<'machine, S>(self, space : &'space S, auth : &'machine S::Auth, machine : &'machine mut Option<Machine<'space, 'machine, S>>) -> Controller<'machine, 'space, LoopStart, S>
    where S : Space<Writer<'space> = W>
    {
        let MachineSpec { exec_permission, prefix_len, buffer, steps_remaining } = self;
        *machine = Some(
            Machine {
                space,
                auth,
                prefix_len,
                buffer,
                retry_remaining   : false,
                steps_remaining,
                exec_permission   : Some(exec_permission),
                pattern_templates : None,

                // this is to protect your computer in debug from blowing your memory. It caused me an OS shutdown.
                #[cfg(debug_assertions)]
                hard_stop : 2000,
            }
        );
        Controller { _state: LoopStart {}, machine: machine }
    }
}

/// The [`Machine`] is only ever interacted with via the [`Controller`].
pub struct Controller<'machine, 'space, State : StateT, S : Space>{
    /// The availible methods are dictated by the type state.
    _state  : State,
    machine : &'machine mut Option<Machine<'space, 'machine, S>>
}

// The following macros are used because it avoids having to care about if self is by value or ref.
// Thes are only ever used internaly
macro_rules! machine_mut {($CONTROLLER:ident) => {unsafe {
    $CONTROLLER.assert_live();
    let machine = $CONTROLLER.machine.as_mut().unwrap_unchecked();
    machine.buffer_invariant();
    machine
}};}
macro_rules! machine_ref {($CONTROLLER:ident) => {unsafe {
    $CONTROLLER.assert_live();
    let machine = $CONTROLLER.machine.as_ref().unwrap_unchecked();
    machine.buffer_invariant();
    machine
}};}


impl<'space, 'machine, State : StateT, S: Space> Controller<'machine, 'space, State, S> {
    /// This is used internally only after a transition has successfully be done.
    #[inline(always)]
    fn next_state<NextState : StateVal>(self, _s : NextState)-> Controller<'machine, 'space, NextState, S> {
        core::debug_assert!(self.machine.is_some());
        #[cfg(debug_assertions)] { self.machine.as_mut().unwrap().hard_stop -=1}
        Controller { _state: NextState::SELF, machine : self.machine }
    }

    /// gives access to a read-only view of the internal machine for debugging.
    #[inline(always)] pub fn inspect_machine(&self) -> &Machine<'space, 'machine, S> { machine_ref!(self) }
    /// Helper method to convert the explict [`Controller`] with type states into the [`MachineHandle`] type.
    #[inline(always)] pub fn to_handle(self) -> MachineHandle<'machine, 'space, S> where State : StateVal{ State::handle_constructor(self) }
    #[inline(always)] pub fn assert_live(&self) {core::debug_assert!(self.machine.is_some());}
}

pub enum LookupCases<'machine, 'space, S : Space> {
    Done,
    ExecsRemaining(Controller<'machine, 'space, LoopStart, S>),
    NonReactiveExec(Controller<'machine, 'space, LoopStart, S>),
    Success(Controller<'machine, 'space, PreTransform, S>),
}
impl<'space, 'machine, S: Space> Controller<'machine, 'space, LoopStart, S> {
    /// lookup the next exec in the space:
    ///   - either all execs were executed([`LookupCases::Done`], execution finishes)
    ///   - or there were deferals ([`LookupCases::ExecsRemaining`];
    ///   - on [`LookupCases::Success`] moves to the next state ( type state moves to [`PreTransform`])
    #[inline(always)]
    pub fn exec_lookup_explicit(self) ->  LookupCases<'machine, 'space, S> { exec_lookup_impl(self) }
}


impl<'space, 'machine, S: Space> Controller<'machine, 'space, PreTransform, S> {
    /// Parse the exec,
    ///
    /// If a value with a shared prefix is found, but does not match syntactically, state moves back to [`LoopStart`] ignoring it;
    ///
    /// if the Reader/Writer permission set cannot be aquired atomically, the state remains [`PreTransform`];
    ///
    /// if it succeeds durring the critical section the callback `at_critical_section` will be called after the transform completes, then moves to [`LoopStart`].
    #[inline(always)]
    pub fn transform_explicit(self, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) -> Result<Controller<'machine, 'space, LoopStart, S>, (Controller<'machine, 'space, PreTransform, S>, S::PermissionErr)>
    { transform_impl(self, at_critical_section) }

    /// If an exec cannot be run, then the current exec can be defered.
    #[inline(always)]
    pub fn defer(self) -> Controller<'machine, 'space, LoopStart, S> { defer_impl(self) }
}


fn exec_lookup_impl<'space, 'machine, S: Space>( controller : Controller<'machine, 'space, LoopStart, S> )
-> LookupCases<'machine, 'space, S>
{
    let Machine { space, prefix_len, buffer, retry_remaining, exec_permission, steps_remaining, .. } = machine_mut!(controller);

    if *steps_remaining == 0 {
        // release the exec space
        *exec_permission = None;
        return LookupCases::Done;
    }
    core::debug_assert!(exec_permission.is_some());

    let exec_wz = space.write_zipper(unsafe { exec_permission.as_mut().unwrap_unchecked() });

    let mut rz = exec_wz.fork_read_zipper();
    rz.descend_to(&buffer[*prefix_len..]);

    if !rz.to_next_val() {
        drop(rz);
        drop(exec_wz);


        if *retry_remaining {
            buffer.truncate(*prefix_len);
            *retry_remaining = false;
            return LookupCases::ExecsRemaining( controller);
        }

        // Sucessfully consumed all execs.  This MeTTa thread is done
        *controller.machine = None;
        return LookupCases::Done
    }
    buffer.truncate(*prefix_len);
    buffer.extend_from_slice(rz.path());
    drop(rz);

    drop(exec_wz);

    let m_mut = machine_mut!(controller);
    let rt = Expr{ ptr: m_mut.buffer.as_mut_ptr() };
    m_mut.pattern_templates = Some(match destructure_exec_expr(m_mut.space, rt) {
        Ok(ok)   => ok,
        Err(_err) => return LookupCases::NonReactiveExec(controller.next_state(LoopStart{})),
    }.collect_inner());

    LookupCases::Success(controller.next_state(PreTransform{}))
}


#[inline(always)]
fn transform_impl<'space, 'machine, S: Space>(controller : Controller<'machine, 'space, PreTransform, S>, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) 
    -> Result<Controller<'machine, 'space, LoopStart, S>, (Controller<'machine, 'space, PreTransform, S>, S::PermissionErr)>
{
    let m_mut = machine_mut!(controller);
    let rt = Expr{ ptr: m_mut.buffer.as_mut_ptr() };

    // take the exec out
    let exec_writer = m_mut.exec_permission.take().unwrap();

    // we need an shared reference for the critical section
    let m_ref = machine_ref!(controller);
    core::debug_assert!( m_ref.pattern_templates.is_some() );
    let (patterns, templates) = unsafe { m_ref.pattern_templates.as_ref().unwrap_unchecked() };

    let maybe_permissions = acquire_exec_permissions(m_ref.space, patterns, templates, m_ref.auth, exec_writer, ||at_critical_section(m_ref));

    // We switch back to the mutable reference
    let Machine { space, prefix_len, buffer, retry_remaining, pattern_templates, steps_remaining, exec_permission, .. } = machine_mut!(controller);

    let ExecPermissions {mut read_map, template_prefixes, mut writers, exec_writer_index, .. } =
    match maybe_permissions {
        Ok(ok)         => ok,
        Err((ew, err)) => { *exec_permission = Some(ew);
                            return Err((controller, err))
                          },
    };

    core::debug_assert!( pattern_templates.is_some() );
    let (patterns, templates) = unsafe { pattern_templates.as_ref().unwrap_unchecked() };

    //Insert the current exec into the read_map
    read_map.set_val_at(unsafe { rt.span().as_ref().unwrap() }, ());

    // remove current exec from space
    {
        let mut wz = space.write_zipper(&mut writers[exec_writer_index]);
        core::debug_assert_eq!(wz.origin_path(), &buffer[..*prefix_len]);
        wz.descend_to(&buffer[*prefix_len..]);
        wz.remove_val(true);
    }

    space.transform_multi_multi(&patterns, &read_map, &templates, &template_prefixes, &mut writers);

    // recover the exec_writer
    *exec_permission = Some(writers.swap_remove(exec_writer_index));

    core::debug_assert!(*steps_remaining > 0);
    (*steps_remaining, *pattern_templates, *retry_remaining) = (*steps_remaining-1, None, false);
    buffer.truncate(*prefix_len);

    Ok(controller.next_state(LoopStart{}))
}

fn defer_impl <'space, 'machine, S: Space>(controller : Controller<'machine, 'space, PreTransform, S>) -> Controller<'machine, 'space, LoopStart, S>
{
    let Machine { pattern_templates, retry_remaining, ..  } = machine_mut!(controller);
    (*retry_remaining,*pattern_templates) = (true, None);
    controller.next_state(LoopStart{})
}


/// Acquires the minimum set of permissions needed to perform an exec by applying the necessary
/// subsumption logic.
///
/// this follows the logic of [`crate::space_temporary::Space::acquire_transform_permissions`]
/// but is too specific to the exec to make general purpose
pub(crate) fn acquire_exec_permissions<'s, E: ExprTrait, S : Space>(
    space            : &'s S,
    patterns         : &[E],
    templates        : &[E],
    auth             : &S::Auth,
    mut exec_writer  : S::Writer<'s>,

    at_critical_section : impl FnOnce(),

) -> Result<ExecPermissions<'s,S>, (S::Writer<'s>, S::PermissionErr)> {
    let make_prefix = |e:&Expr|  unsafe { e.prefix().unwrap_or_else(|_| e.span()).as_ref().unwrap() };

    // this version of the function needs to remember what index holds the initial writer


    // ************************************************************************
    // Writer subsumption logic (No permissions acquired yet)
    // ************************************************************************

    //Make a vec of template paths, sorted from shortest to longest
    // `(path, template_idx, writer_slot_idx)`
    let mut template_path_table: Vec<(&[u8], usize, usize)> = templates.iter().enumerate().map(|(i, template)|{
        let path = make_prefix(&template.borrow());
        (path, i, 0)
    }).collect();

    // insert initial
    let wz = space.write_zipper(&mut exec_writer);
    let exec_path = wz.origin_path().to_owned();
    drop(wz);
    let last_index = template_path_table.len();
    template_path_table.push((&exec_path, template_path_table.len(), 0));
    // template_path_table.push((make_prefix(&Expr { ptr: exec_path.as_mut_ptr()}), template_path_table.len(), 0));

    // We want the exec_writer to be most subsuming, so it must start at index 0
    template_path_table.swap(0, last_index);
    template_path_table.sort_by(|a, b| a.0.len().cmp(&b.0.len()));

    let mut exec_writer_index = usize::MAX;

    //Find the set of least-common-denominator template prefixes
    let mut writer_slots: Vec<&[u8]> = Vec::with_capacity(templates.len());
    for (path, _template_idx, writer_slot_idx) in template_path_table.iter_mut() {
        let mut subsumed = false;
        for (slot_idx, slot_path) in writer_slots.iter().enumerate() {
            let overlap = pathmap::utils::find_prefix_overlap(path, slot_path);
            if overlap == slot_path.len() {
                *writer_slot_idx = slot_idx;
                subsumed = true;
                break
            }
        }
        if !subsumed {
            if *_template_idx == last_index {
                exec_writer_index = writer_slots.len()
            }
            *writer_slot_idx = writer_slots.len();
            writer_slots.push(path);
        } else if *_template_idx == last_index {
            // force a permission error
            match space.new_writer(&exec_path, auth) {
                Ok(_)  => core::unreachable!(),
                Err(e) => return Err((exec_writer, e)),
            };
        }
    }
    core::assert_ne!(exec_writer_index, usize::MAX);

    let mut template_prefixes = vec![(0, 0); templates.len()];
    for (_, template_idx, writer_slot_idx) in template_path_table {

        // we don't want the initial_writer to be included in the templates.
        if template_idx != last_index {
            let incremental_path_start = writer_slots[writer_slot_idx].len();
            template_prefixes[template_idx] = (incremental_path_start, writer_slot_idx);
        }
    }

    // ************************************************************************
    // Permission Acquisition
    // ************************************************************************

    let mut read_map = PathMap::new();
    let mut writers = Vec::with_capacity(writer_slots.len());

    let mut some_initial_writer = Some(exec_writer);

    let new_multiple_result = space.new_multiple(|perm_head| {
        //Make the "ReadMap" by copying each pattern from the space
        for pat in patterns {
            let path = make_prefix(&pat.borrow());

            if path.len() >= exec_path.len() // if it is less we don't want to risk doing a string compare, so we shortcut
            && pathmap::utils::find_prefix_overlap(path, &exec_path) == exec_path.len() {
                // the initial writer has not been taken yet, so this is infalible
                let writer = some_initial_writer.as_mut().unwrap();
                let mut wz = space.write_zipper(writer);
                wz.descend_to(&path[exec_path.len()..]);

                // I might be able to do something more elegant if the trait bounds were different.
                let s_map = wz.take_map(true);
                if let Some(map) = s_map {
                    wz.graft_map(map.clone());
                    let mut wz_map = read_map.write_zipper_at_path(path);
                    wz_map.graft_map(map);
                }
            } else {
                // if it subsumes our exec_writer we _want_ the error

                let mut reader = perm_head.new_reader(path, auth)?;
                let rz = space.read_zipper(&mut reader);

                let mut wz = read_map.write_zipper_at_path(path);
                wz.graft(&rz);
            }
        }

        //Acquire writers at each slot, knowing where any conflicts are with external clients
        for (i, path) in writer_slots.iter().enumerate() {
            if i == exec_writer_index {
                let siw = some_initial_writer.take();
                let s = siw.map(|iw| writers.push(iw));

                #[cfg(debug_assertions)] s.expect("This should only unwrap once");

            } else {
                let writer = perm_head.new_writer(path, auth)?;
                writers.push(writer);
            }
        }

        at_critical_section();
        Ok(())
    });
    if let Err(err) = new_multiple_result { return Err (match some_initial_writer {
        Some(ew) => (ew, err),
        None     => { // we should only be here if the new_multiple put the exec_writer into the writers vec
                      (writers.swap_remove(exec_writer_index), err)
                    },
    })};

    Ok( ExecPermissions {
        space : core::marker::PhantomData,
        read_map,
        template_prefixes,
        writers,
        exec_writer_index
    })
}

pub(crate) struct ExecPermissions<'s, S: Space> {
    /// This is here to accurately preserve the lifetime
    pub(crate) space             : core::marker::PhantomData<&'s S>,
    /// A PathMap in which all readers can be acquired
    pub(crate) read_map          : PathMap<()>,
    /// A vec of `(incremental_path_start, writer_idx)`, corresponding to the `templates` where:
    ///  - `incremental_path_start`: The index in the full template path for the start of the part of the path
    ///     that is not subsumed by the writer's root path.
    ///  - `writer_idx`: The index into `writers` for the write permssion to use for this expr
    pub(crate) template_prefixes : Vec<(usize, usize)>,
    /// A vector of [Space::Writer] permission objects
    pub(crate) writers           : Vec<S::Writer<'s>>,
    /// the writer at this index needs to be recovered
    pub(crate) exec_writer_index : usize,
}











// ///////////////////
// SEMANTIC MODEL  //
// /////////////////

// there have been changes to the following :
//     a max iteration step count has been added,
//     the exec prefix permission is no longer dropped meaning that subsumption has an exceptional case where a reader/writer can never subsume the exec prefix.
//
// par for thread in threads
//   'from_start
//   let it = space.at(`[4] exec [2] `thread``)
//   'from_current
//   let stmt = it.next(`(exec (`thread` $loc) $patterns $templates)`)
//   try
//     atomic
//       let read_permissions = get_read_permissions(stmt)
//       let write_permissions = get_write_permissions(stmt)
//     space.transform(stmt, read_permissions, write_permissions)
//     goto 'from_start
//   except PermissionError
//     goto 'from_current
//   except Exception as e
//     space.add(`(exec (`thread` $loc) `e`)`)
//     goto 'done
//   finally
//     drop(read_permissions)
//     drop(write_permissions)
// 'done

// this models the the behavior of the upper semantic model as closely as described, but some changes have been made.

/// The basic implementation using type state; comments show points one could include intermidiate actions like journaling
pub(crate) fn metta_calculus_impl_statemachine_poc<'space, S: Space>(
    space               : &'space S,
    thread_id_sexpr_str : &str,
    step_cnt        : usize,
    auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
    let mut machine = None;
    let mut start_controller =
        Machine::spec_args(space, thread_id_sexpr_str, step_cnt, auth).init_in_exec(&mut machine)?;

    'process_execs : loop {
        let lookup_success = match start_controller.exec_lookup_explicit() {
            LookupCases::Success(lookup_success) => lookup_success,
            LookupCases::Done                         => return Ok(()),
            LookupCases::NonReactiveExec(remaining) |
            LookupCases::ExecsRemaining(remaining)    => {
                                                           start_controller = remaining;
                                                           continue 'process_execs;
                                                         },
        };
        // close the loop
        start_controller = lookup_success.transform_or_defer(|_|{/* journal transform in critical section */});
    }
}













// ////////////////////////////////////////////////////////////////
// ! the following are helper methods, the core logic is above. //
// //////////////////////////////////////////////////////////////

/// The basic implementation using [`MachineHandle`]. one could modify it to match on the handle.
#[allow(unused)]
pub(crate) fn metta_calculus_impl_statemachine_poc_machine_handle<'space, S: Space>(
    space               : &'space S,
    thread_id_sexpr_str : &str,
    step_cnt            : usize,
    auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
    type MH<'m, 's, S> = MachineHandle<'m, 's, S>;
    let mut machine = None;
    let mut handle  = Machine::spec_args( space, thread_id_sexpr_str, step_cnt, auth ).init_in_exec(&mut machine)?.to_handle();

    'process_execs : loop {
        handle = match handle.advance() {
            CF::Continue(c) => c,
            CF::Break(())   => return Ok(()),
        };
    }
}

impl<'machine, 'space, S : Space> MachineHandle<'machine, 'space, S> {
    // the default advance strategy is to ignore "Errors" and continue running without modifying the space
    #[inline(always)]
    pub fn advance(self) -> ControlFlow<(), Self> {
        CF::Continue(match self {
            MachineHandle::LoopStart      (controller) => if let CF::Continue(h) = controller.exec_lookup() {h} else {return CF::Break(());},
            MachineHandle::PreTransform   (controller) => controller.transform_or_defer(|_|{}).to_handle(),
        })
    }
}

impl<'space, 'auth, 'arg, S : Space> MachineSpecArgs<'space, 'auth, 'arg, S> {
    /// Initializes the machine directly into the [`LoopStart`] state.
    /// the `place` argument value should be [`Option::None`], as it will be replaced with the new [`Machine`] inside a [`Some`].
    #[inline(always)]
    pub fn init<'machine>(self, machine : &'auth mut Option<Machine<'space,'auth, S>>) -> std::result::Result<Controller<'auth, 'space, LoopStart, S>, S::PermissionErr> {
        let (space, auth) = (self.space, self.auth);
        self.make().map(|ms|ms.init(space, auth, machine))
    }

    /// helper method where the return value is the same as [`Self::make`], but the error type is upcast to an [`crate::space::ExecError`]
    #[inline(always)]
    pub fn make_in_exec(self) -> Result<MachineSpec<S::Writer<'space>>, ExecError<S>> {
        let space = self.space;
        self.make().map_err(|perm_err|ExecError::perm_err(space, perm_err))
    }
    
    /// helper method that has the same return type as [`Self::init`], but it upcasts the error to an [`ExecError`]
    #[inline(always)]
    pub fn init_in_exec(self, machine : &'auth mut Option<Machine<'space,'auth, S>>) -> std::result::Result<Controller<'auth, 'space, LoopStart, S>, ExecError<S>> {
        let (space, auth) = (self.space, self.auth);
        self.make_in_exec().map(|ms|ms.init(space, auth, machine))
    }
}

impl<'space, 'machine, S: Space> Controller<'machine, 'space, LoopStart, S> {
    /// Calls [`Self::exec_lookup_explicit`] and converts the nested cases that are type states into a [`MachineHandle`]
    #[inline(always)]
    pub fn exec_lookup(self)
    ->  ControlFlow<(), MachineHandle<'machine, 'space, S>>
    {
        match self.exec_lookup_explicit() {
            LookupCases::Success(c)                => CF::Continue(MachineHandle::PreTransform(c)),
            LookupCases::Done                      => CF::Break(()),
            LookupCases::NonReactiveExec(remaining) |
            LookupCases::ExecsRemaining(remaining) => CF::Continue(MachineHandle::LoopStart(remaining)),
        }
    }
}

impl<'space, 'machine, S: Space> Controller<'machine, 'space, PreTransform, S> {
    /// ignores "Errors" from [`Self::transform_explicit`]
    #[inline(always)]
    pub fn transform(self, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) -> MachineHandle<'machine, 'space, S> {
        self.transform_explicit(at_critical_section).map_or_else(|(c,_)|c.to_handle(), Controller::to_handle) 
    }

    /// calls [`Self::defer`] on the case where a [`Self::transform`] would have not changed state on a falure to run an exec failing to aquire it's permissions.
    #[inline(always)]
    pub fn transform_or_defer(self, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>))->Controller<'machine, 'space, LoopStart, S> {
        self.transform_explicit(at_critical_section).unwrap_or_else(|(c,_)|c.defer())
    }
}
