//! The Metta Calculus [`Machine`] is the state machine that allows running the Calculus 
//! while being able to run outside logic while maintaing the internal consistancy on the Calculus state.



use std::ops::ControlFlow;
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
    ExecsRemaining        "There were conflicts that have been skipped; \n\ncontinue to restart the loop.",
    PreTransform          "Permission was droped; \n\nnext, try to run the transform",
}

pub struct Done;

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

    steps_remaining        : usize,

    // /////////////
    // LOOP VARS //
    // ///////////

    /// [`Some`] before removal of the current exec, or the reinsertion on a deferal; [`None`] once the removal/reinsertion is complete.
    exec_permission     : Option<<S as Space>::Writer<'space>>,
    /// This holds the patterns and templates until the current exec either succeeds or sucessfully defers.
    pattern_templates   : Option<(Vec<Expr>, Vec<Expr>)>,

}

pub struct MachineSpec<W>{
    // space               : &'space S,
    exec_permission     : W,
    // auth                : &'auth S::Auth,
    prefix_len          : usize,
    buffer              : Vec<u8>,
    steps_remaining     : usize,
}
impl<'space, 'machine, S: Space> Machine<'space, 'machine, S> {

    pub fn machine_spec(
        space               : &'space S,
        thread_id_sexpr_str : &str,
        steps               : usize,
        auth                : &'machine S::Auth
    ) -> Result<MachineSpec<S::Writer<'space>>, S::PermissionErr> {
        // //GOAT, MM2-Syntax.  we need to lift these patterns out as constants so we can tweak the MM2 syntax without hunting through the implementation
        // //
        // // (exec (<location> $priority) $patterns $templates)

        let prefix_expr = space.sexpr_to_expr(&format!("(exec ({} $) $ $)", thread_id_sexpr_str)).unwrap();
        let prefix = unsafe { prefix_expr.borrow().prefix().unwrap().as_ref().unwrap() };

        let prefix_len = prefix.len();
        let buffer     = Vec::from(prefix);

        let writer = space.new_writer_retry(prefix, 1000, auth)?;

        Ok(MachineSpec { exec_permission: writer, prefix_len, buffer, steps_remaining: steps })
    }

    /// Initializes the machine in the [`LoopStart`] state.
    /// the `place` argument value should be [`Option::None`], as it will be replaced with the new [`Machine`] inside a [`Some`].
    #[inline(always)]
    pub fn init(
        space               : &'space S,
        auth                : &'machine S::Auth,
        machine             : &'machine mut Option<Self>,
        machine_spec        : MachineSpec<S::Writer<'space>>,
    ) -> Controller<'machine, 'space, LoopStart, S> {



        let MachineSpec { exec_permission, prefix_len, buffer, steps_remaining } = machine_spec;

        let retry_remaining = false;

        *machine = Some(
            Machine {
                space,
                auth,
                prefix_len,
                buffer,
                retry_remaining,
                steps_remaining   : steps_remaining,
                exec_permission   : Some(exec_permission),
                pattern_templates : None,
            }
        );
        Controller { _state: LoopStart {}, machine }
    }

    // The following methods are primarily here for inspection by users, without fear of breaking the integrity of the state machine.
    #[inline(always)] pub fn prefix         (&self) -> &[u8]             { &self.buffer[0..self.prefix_len]}
    /// on [`None`] the buffer only contains the prefix, on [`Some`] the last exec was found on lookup is output.
    #[inline(always)] pub fn current_exec   (&self) -> Option<&[u8]>     { (self.buffer.len() > self.prefix_len).then_some(&self.buffer[..]) }
    /// checks if at least one Deferal has be sheduled
    #[inline(always)] pub fn retry_remaining(&self) -> bool              { self.retry_remaining }
    #[inline(always)] pub fn space          (&self) -> &'space S         { self.space }
    #[inline(always)] pub fn auth           (&self) -> &'machine S::Auth { self.auth }
}

impl<'space, W> MachineSpec<W> {
pub fn init<'machine, S>(self, space : &'space S, auth : &'machine S::Auth, machine : &'machine mut Option<Machine<'space, 'machine, S>>) -> Controller<'machine, 'space, LoopStart, S> 
    where S : Space<Writer<'space> = W>
    {
        Machine::init(space, auth, machine, self)
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
macro_rules! machine_mut {
($CONTROLLER:ident) => {unsafe {
    core::debug_assert!($CONTROLLER.machine.is_some());
    let machine = $CONTROLLER.machine.as_mut().unwrap_unchecked();
    // This Safety invariant must _always_ be true, so might as well do it here.
    core::debug_assert!(machine.buffer.len()>=machine.prefix_len);
    machine
}};
}
macro_rules! machine_ref {
($CONTROLLER:ident) => {unsafe {
    core::debug_assert!($CONTROLLER.machine.is_some());
    let machine = $CONTROLLER.machine.as_ref().unwrap_unchecked();
    // This Safety invariant must _always_ be true, so might as well do it here.
    core::debug_assert!(machine.buffer.len()>=machine.prefix_len);
    machine
}};
}

impl<'space, 'machine, State : StateT, S: Space> Controller<'machine, 'space, State, S> {
    /// This is used internally only after a transition has successfully be done.
    #[inline(always)]
    fn next_state<NextState : StateVal>(self, _s : NextState)-> Controller<'machine, 'space, NextState, S> {
        core::debug_assert!(self.machine.is_some());
        Controller { _state: NextState::SELF, machine : self.machine }
    }

    #[inline(always)]
    pub fn inspect_machine(&self)->&Machine<'space, 'machine, S> {
        machine_ref!(self)
    }

    /// Helper method to convert the explict [`Controller`] with type states into the [`MachineHandle`] type.
    #[inline(always)]
    pub fn to_handle(self)->MachineHandle<'machine, 'space, S> where State : StateVal{
        State::handle_constructor(self)
    }
}

pub enum LookupBaseCases<'machine, 'space, S : Space> {
    Done,
    ExecsRemaining(Controller<'machine, 'space, ExecsRemaining, S>),
}
impl<'space, 'machine, S: Space> Controller<'machine, 'space, LoopStart, S> {
    /// lookup the next exec in the space:
    /// - on [`ControlFlow::Break`]
    ///   - either all execs were executed([`LookupBaseCases::Done`], execution finishes)
    ///   - or there were deferals ([`LookupBaseCases::ExecsRemaining`], type state moves to [`ExecsRemaining`]);
    ///
    /// - on [`ControlFlow::Continue`] ( type state moves to [`PreTransform`])
    #[inline(always)]
    pub fn exec_lookup(self) ->  ControlFlow<LookupBaseCases<'machine, 'space, S>, Controller<'machine, 'space, PreTransform, S>,> { exec_lookup_impl(self) }

    /// Calls [`Self::exec_lookup`] and converts the nested cases that are type states into a [`MachineHandle`]
    #[inline(always)]
    pub fn exec_lookup_to_handle(self)
    ->  ControlFlow<(), MachineHandle<'machine, 'space, S>>
    {
        match self.exec_lookup() {
            ControlFlow::Continue(c) => CF::Continue(MachineHandle::PreTransform(c)),
            ControlFlow::Break(LookupBaseCases::Done) => CF::Break(()),
            ControlFlow::Break(LookupBaseCases::ExecsRemaining(remaining)) => CF::Continue(MachineHandle::ExecsRemaining(remaining)),
        }
    }
}


fn exec_lookup_impl<'space, 'machine, S: Space>( controller : Controller<'machine, 'space, LoopStart, S> )
-> ControlFlow< LookupBaseCases<'machine, 'space, S>, Controller<'machine, 'space, PreTransform, S>,>
{
    let Machine { space, prefix_len, buffer, retry_remaining, exec_permission, steps_remaining, .. } = machine_mut!(controller);
    core::debug_assert!(exec_permission.is_some());

    if *steps_remaining == 0 {
        return CF::Break(LookupBaseCases::Done);
    }

    let mut exec_wz = space.write_zipper(unsafe { exec_permission.as_mut().unwrap_unchecked() });

    let mut rz = exec_wz.fork_read_zipper();
    rz.descend_to(&buffer[*prefix_len..]);

    if !rz.to_next_val() {
        drop(rz);
        drop(exec_wz);


        if *retry_remaining {
            return CF::Break(LookupBaseCases::ExecsRemaining( controller.next_state(ExecsRemaining {})));
        }

        // Sucessfully consumed all execs.  This MeTTa thread is done
        *controller.machine = None;
        return CF::Break(LookupBaseCases::Done)
    }
    buffer.truncate(*prefix_len);
    buffer.extend_from_slice(rz.path());
    drop(rz);

    // Remove expr, which means we are "claiming" it
    exec_wz.descend_to(&buffer[*prefix_len..]);
    exec_wz.remove_val();

    drop(exec_wz);
    CF::Continue(controller.next_state(PreTransform{}))
}

impl<'space, 'machine, S: Space> Controller<'machine, 'space, ExecsRemaining, S> {
    /// restart the [`Machine`] from the beginning, change to [`LoopStart`]
    #[inline(always)]
    pub fn continue_loop(self) ->  Controller<'machine, 'space, LoopStart, S> { continue_loop_impl(self) }
}

fn continue_loop_impl<'space, 'machine, S: Space>(controller : Controller<'machine, 'space, ExecsRemaining, S>) -> Controller<'machine, 'space, LoopStart, S> {
    let Machine { prefix_len, buffer, exec_permission, .. } = machine_mut!(controller);
    core::debug_assert!(exec_permission.is_none());

    buffer.truncate(*prefix_len);
    controller.next_state(LoopStart {})
}

pub enum TransformErr<'machine, 'space, S : Space> {
    Syntax    ((Controller<'machine, 'space, LoopStart,    S>, ExecSyntaxError )),
    Permission((Controller<'machine, 'space, PreTransform, S>, S::PermissionErr)),
}
impl<'space, 'machine, S: Space> Controller<'machine, 'space, PreTransform, S> {
    /// Parse the exec,
    ///
    /// on a syntax err the state moves back to [`LoopStart`];
    ///
    /// if the Reader/Writer permission set cannot be aquired atomically, the state remains [`PreTransform`];
    ///
    /// if it succeeds durring the critical section the callback `at_critical_section` will be called after the transform completes, then moves to [`LoopStart`].
    #[inline(always)]
    pub fn transform(self, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) -> Result<Controller<'machine, 'space, LoopStart, S>, TransformErr<'machine, 'space, S>,>{ transform_impl(self, at_critical_section) }


    /// If an exec cannot be run, then the current exec can be defered by reinserting it into the space.
    /// Aquiring the [`DeferGuard`] means we have the permission for reinsertion:
    /// - on [`Ok`]  the permission is held in the [`Machine`], state becomes [`DeferGuard`];
    /// - on [`Err`] the [`Machine`] stays in the [`PreTransform`] state.
    #[inline(always)]
    pub fn defer(self) -> Controller<'machine, 'space, LoopStart, S> { 
        defer_impl(self)
    }
}

fn transform_impl<'space, 'machine, S: Space>(controller : Controller<'machine, 'space, PreTransform, S>, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) -> Result<Controller<'machine, 'space, LoopStart, S>, TransformErr<'machine, 'space, S>,> {
    let m_mut = machine_mut!(controller);
    let rt = Expr{ ptr: m_mut.buffer.as_mut_ptr() };
    // if this code get revisited we want to avoid this branch
    if m_mut.pattern_templates.is_none() {
        m_mut.pattern_templates = Some(match destructure_exec_expr(m_mut.space, rt) {
            Ok(ok)   => ok,
            Err(err) => return Err(TransformErr::Syntax((controller.next_state(LoopStart{}), err))),
        }.collect_inner());
    }

    // take the exec out
    let exec_writer = m_mut.exec_permission.take().unwrap();

    // we need an shared reference for the critical section
    let m_ref = machine_ref!(controller);
    core::debug_assert!( m_ref.pattern_templates.is_some() );
    let (patterns, templates) = unsafe { m_ref.pattern_templates.as_ref().unwrap_unchecked() };

    let ExecPermissions {mut read_map, template_prefixes, mut writers, exec_writer_index, .. } = 
    match acquire_exec_permissions(m_ref.space, patterns, templates, m_ref.auth, exec_writer, ||at_critical_section(m_ref)) {
        Ok(ok)   => ok,
        Err(err) => return Err(TransformErr::Permission((controller, err))),
    };

    // We switch back to the mutable reference
    let Machine { space, prefix_len, buffer, retry_remaining, pattern_templates, steps_remaining, exec_permission, .. } = machine_mut!(controller);
    core::debug_assert!( pattern_templates.is_some() );
    let (patterns, templates) = unsafe { pattern_templates.as_ref().unwrap_unchecked() };

    //Insert the current exec into the read_map
    read_map.set_val_at(unsafe { rt.span().as_ref().unwrap() }, ());

    // remove current exec from space
    {
        let mut wz = space.write_zipper(&mut writers[exec_writer_index]);
        core::debug_assert_eq!(wz.path(), &buffer[..*prefix_len]);
        wz.descend_to(&buffer[*prefix_len..]);        
    }

    space.transform_multi_multi(&patterns, &read_map, &templates, &template_prefixes, &mut writers);

    // recover the exec_writer
    *exec_permission = Some(writers.swap_remove(exec_writer_index));
 
    core::debug_assert!(*steps_remaining > 0);
    *steps_remaining -= 1;
    *pattern_templates = None;
    *retry_remaining = false;
    buffer.truncate(*prefix_len);

    Ok(controller.next_state(LoopStart{}))
}

fn defer_impl <'space, 'machine, S: Space>(controller : Controller<'machine, 'space, PreTransform, S>) -> Controller<'machine, 'space, LoopStart, S>
{
    let Machine { pattern_templates, retry_remaining, ..  } = machine_mut!(controller);
    
    *retry_remaining   = true;
    *pattern_templates = None;

    controller.next_state(LoopStart{})
}

impl<'machine, 'space, S : Space> MachineHandle<'machine, 'space, S> {
/// This gives the basic logic of metta_calculus via the [`MachineHandle`] with no retries, but tries to defer on a failed transform. Otherwise it bubbles up an error
pub fn advance(self) -> ControlFlow<Result<(), (Self, ExecError<S>)>, Self> {
    type MH<'m, 's, S> = MachineHandle<'m, 's, S>;
    ControlFlow::Continue(match self {
        MH::LoopStart            (controller) => if let CF::Continue(h) = controller.exec_lookup_to_handle() {h} else {return CF::Break(Ok(()));}
                                                 ,
        MH::ExecsRemaining       (controller) => controller.continue_loop().to_handle(),
        MH::PreTransform         (controller) => match controller.transform(|_|{/* journal transform in critical section */}) {
                                                     Ok(ok)                                 => ok.to_handle(),
                                                     Err(TransformErr::Syntax((c,e)))       => return ControlFlow::Break(Err((c.to_handle(), ExecError::Syntax(e)))),
                                                     Err(TransformErr::Permission((c, _e))) => c.defer().to_handle(),        
                                                 },
    })
}
}

/// The basic implementation using type state and including retry logic. comments show points one could include intermidiate actions like journaling
#[allow(unused)]
pub(crate) fn metta_calculus_impl_statemachine_poc<'space, S: Space>(
    space               : &'space S,
    thread_id_sexpr_str : &str,
    max_retries         : usize,
    mut step_cnt        : usize,
    auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
    let mut machine = None;
    let mut start_controller = 
        Machine::machine_spec(space, thread_id_sexpr_str, step_cnt, auth).map_err(|perm_err|ExecError::perm_err(space, perm_err))?
        .init(space, auth, &mut machine);

    'process_execs : loop {
        let lookup_success = match start_controller.exec_lookup() {
            CF::Continue(lookup_success)                          => lookup_success,
            CF::Break(LookupBaseCases::Done)                      => return Ok(()),
            CF::Break(LookupBaseCases::ExecsRemaining(remaining)) => {
                                                                       start_controller = remaining.continue_loop();
                                                                       continue 'process_execs;
                                                                     },
        };
        // close the loop
        start_controller = match lookup_success.transform(|_|{/* journal transform in critical section */}) {
            Ok(ok)                                 => ok,
            Err(TransformErr::Syntax((_c,e)))      => return Err(ExecError::Syntax(e)),
            Err(TransformErr::Permission((c, _e))) => { c.defer()},
        };
    }
}

/// The basic implementation using [`MachineHandle`]
#[allow(unused)]
pub(crate) fn metta_calculus_impl_statemachine_poc_machine_handle<'space, S: Space>(
    space               : &'space S,
    thread_id_sexpr_str : &str,
    max_retries         : usize,
    mut step_cnt        : usize,
    auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
    type MH<'m, 's, S> = MachineHandle<'m, 's, S>;
    let mut machine = None;
    let mut handle = 
        Machine::machine_spec(space, thread_id_sexpr_str, step_cnt, auth).map_err(|perm_err|ExecError::perm_err(space, perm_err))?
        .init(space, auth, &mut machine).to_handle();

    'process_execs : loop {
        handle = match handle.advance() {
            ControlFlow::Continue(c) => c,
            ControlFlow::Break(b)    => return b.map_err(|(_,e)|e),
        };
    }
}



// ///////////////////
// SEMANTIC MODEL //
// /////////////////
//
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

// this models the the behavior of the upper semantic model as closely as described, but some changes have been made. The 
#[allow(unused)]
pub(crate) fn metta_calculus_model<'space, S: Space>(
space               : &'space S,
thread_id_sexpr_str : &str,
mut step_cnt        : usize,
auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
    let mut machine = None;
    let mut start_controller = 
        Machine::machine_spec(space, thread_id_sexpr_str, step_cnt, auth).map_err(|perm_err|ExecError::perm_err(space, perm_err))?
        .init(space, auth, &mut machine);

    // const MAX_RETRIES : usize = usize::MAX;
    'process_execs : loop {
        let removed = match start_controller.exec_lookup() {
            CF::Continue(removed)                                 => removed,
            CF::Break(LookupBaseCases::Done)                      => return Ok(()),
            CF::Break(LookupBaseCases::ExecsRemaining(remaining)) => {
                                                                       start_controller = remaining.continue_loop();
                                                                       continue 'process_execs;
                                                                     },
        };
        // journal removal

        // close the loop
        start_controller = match removed.transform(|_|{/* journal transform in critical section */}) {
            Ok(ok)                                 => ok,
            Err(TransformErr::Syntax((_c,e)))      => return Err(ExecError::Syntax(e)),
            Err(TransformErr::Permission((c, _e))) => { c.defer()},
        };
    }
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
) -> Result<ExecPermissions<'s,S>, S::PermissionErr> {
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
    let mut exec_path = wz.path().to_owned();
    drop(wz);
    let last_index = template_path_table.len();
    template_path_table.push((make_prefix(&Expr { ptr: exec_path.as_mut_ptr()}), template_path_table.len(), 0)); 

    // Is the swap needed?
    template_path_table.swap(0, last_index);
    template_path_table.sort_by(|a, b| a.0.len().cmp(&b.0.len()));
    
    // we need to remeber where the initial writer is for recovering it later.
    let mut initial_position = 0;
    while last_index != template_path_table[initial_position].1 {
        initial_position += 1;
    }

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
                Ok(_) => core::unreachable!(),
                Err(e) => return Err(e),
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

    space.new_multiple(|perm_head| {

        //Make the "ReadMap" by copying each pattern from the space
        for pat in patterns {
            let path = make_prefix(&pat.borrow());

            let mut reader = perm_head.new_reader(path, auth)?;
            let rz = space.read_zipper(&mut reader);

            let mut wz = read_map.write_zipper_at_path(path);
            wz.graft(&rz);
        }

        //Acquire writers at each slot, knowing we any conflicts are with external clients
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
    })?;

    trace!(target: "transform", "templates {:?}", templates);
    trace!(target: "transform", "prefixes {:?}", template_prefixes);

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
