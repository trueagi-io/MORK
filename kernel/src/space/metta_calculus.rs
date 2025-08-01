//! The Metta Calculus [`Machine`] is the state machine that allows running the Calculus 
//! while being able to run outside logic while maintaing the internal consistancy on the Calculus state.



use std::ops::ControlFlow;
type CF<B,C> = ControlFlow<B,C>;
use crate::space::*;

macro_rules! states {
($( $STATE:ident $DOC:literal,)+) => {
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
ExecRemovalPermission "The permission for the exec's prefix was aquired; \n\nnext, lookup the next exec to run.",
ExecsRemaining        "There were conflicts that have been skipped; \n\ncontinue to restart the loop.",
ExecRemovedGuard      "The current exec was removed from the space (the state of the space has been modified), but the permission is still being held; \n\n next, immediatly drop the permission and construct transform arguments.",
PreTransform          "Permission was droped; \n\nnext, try to run the transform",
DeferGuard            "The permission for defering is being held; \n\nnext, reinsert to defer execution of current exec.",
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
impl<'space, 'machine, S: Space> Machine<'space, 'machine, S> {
/// Initializes the machine in the [`LoopStart`] state.
/// the `place` argument value should be [`Option::None`], as it will be replaced with the new [`Machine`] inside a [`Some`].
#[inline(always)]
pub fn init(
    machine             : &'machine mut Option<Self>,
    space               : &'space S,
    thread_id_sexpr_str : &str,
    steps               : usize,
    auth                : &'machine S::Auth,
) -> Controller<'machine, 'space, LoopStart, S> {

    //GOAT, MM2-Syntax.  we need to lift these patterns out as constants so we can tweak the MM2 syntax without hunting through the implementation
    //
    // (exec (<location> $priority) $patterns $templates)
    let prefix_expr = space.sexpr_to_expr(&format!("(exec ({} $) $ $)", thread_id_sexpr_str)).unwrap();
    let prefix = unsafe { prefix_expr.borrow().prefix().unwrap().as_ref().unwrap() };

    let prefix_len = prefix.len();
    let buffer     = Vec::from(prefix);

    let retry_remaining = false;

    *machine = Some(
        Machine {
            space,
            auth,
            prefix_len,
            buffer,
            retry_remaining,
            steps_remaining   : steps,
            exec_permission   : None,
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

impl<'space, 'machine, S: Space> Controller<'machine, 'space, LoopStart, S> {
/// Attempt to get the permission for the next exec,
/// - on [`Ok`]  the permission is held in the [`Machine`], state becomes [`ExecRemovalPermission`];
/// - on [`Err`] the [`Machine`] stays in the [`LoopStart`] state.
#[inline(always)]
pub fn exec_permission(self)
-> Result<
    Controller<'machine, 'space, ExecRemovalPermission, S>,
    (Self, <S as Space>::PermissionErr),
> {
    let Machine { space, auth, prefix_len, buffer, exec_permission, .. } = machine_mut!(self);
    core::debug_assert!(exec_permission.is_none());

    match space.new_writer(&buffer[..*prefix_len], auth) {
        Ok(writer) => { *exec_permission = Some(writer);
                        Ok(self.next_state(ExecRemovalPermission{}))
                      }
        Err(error) => Err((self,error)),
    }
}

/// Adds retry logic to [`Self::exec_permission`];
/// retry logic should mirror [`Controller<'machine, 'space, PreTransform, S>::defer_guard_with_retries`].
#[inline(always)]
pub fn exec_permission_with_retries(mut self, max_retries : usize)
-> Result<
    Controller<'machine, 'space, ExecRemovalPermission, S>,
    (Self, <S as Space>::PermissionErr),
> {
    let mut err = None;
    for _each in 0..max_retries.max(1) {
        match self.exec_permission() {
            Ok(ok)     => return Ok(ok),
            Err((c,e)) => { (self, err) = (c, Some(e))},
        };
        std::thread::sleep(core::time::Duration::from_micros(500));
    }
    Err((self, err.unwrap()))
}
}

pub enum LookupBaseCases<'machine, 'space, S : Space> {
Done,
ExecsRemaining(Controller<'machine, 'space, ExecsRemaining, S>),
}
impl<'space, 'machine, S: Space> Controller<'machine, 'space, ExecRemovalPermission, S> {
    /// lookup the next exec in the space:
    /// - on [`ControlFlow::Break`] permission is dropped:
    ///   - either all execs were executed([`LookupBaseCases::Done`], execution finishes)
    ///   - or there were deferals ([`LookupBaseCases::ExecsRemaining`], type state moves to [`ExecsRemaining`]);
    ///
    /// - on [`ControlFlow::Continue`] the permission is dropped, unlocking the space at the prefix ( type state moves to [`ExecRemovedGuard`])
    #[inline(always)]
    pub fn exec_lookup(self) ->  ControlFlow<LookupBaseCases<'machine, 'space, S>, Controller<'machine, 'space, ExecRemovedGuard, S>,> { exec_lookup_impl(self) }


    /// Calls [`Self::exec_lookup`] and converts the nested cases that are type states into a [`MachineHandle`]
    #[inline(always)]
    pub fn exec_lookup_to_handle(self)
    ->  ControlFlow<(), MachineHandle<'machine, 'space, S>>
    {
        match self.exec_lookup() {
            ControlFlow::Continue(c) => CF::Continue(MachineHandle::ExecRemovedGuard(c)),
            ControlFlow::Break(LookupBaseCases::Done) => CF::Break(()),
            ControlFlow::Break(LookupBaseCases::ExecsRemaining(remaining)) => CF::Continue(MachineHandle::ExecsRemaining(remaining)),
        }
    }
}


fn exec_lookup_impl<'space, 'machine, S: Space>( controller : Controller<'machine, 'space, ExecRemovalPermission, S> ) 
-> ControlFlow< LookupBaseCases<'machine, 'space, S>, Controller<'machine, 'space, ExecRemovedGuard, S>,>
{
    let Machine { space, prefix_len, buffer, retry_remaining, exec_permission, steps_remaining, .. } = machine_mut!(controller);
    core::debug_assert!(exec_permission.is_some());

    // this might not be the best place to do this, but until the refactor is done, this gives the correct semantics without changing function signatures
    if *steps_remaining == 0 {
        return CF::Break(LookupBaseCases::Done);
    } 

    let mut exec_wz = space.write_zipper(unsafe { exec_permission.as_mut().unwrap_unchecked() });

    let mut rz = exec_wz.fork_read_zipper();
    rz.descend_to(&buffer[*prefix_len..]);

    if !rz.to_next_val() {
        drop(rz);
        drop(exec_wz);
        // unblock this as soon as possible
        *exec_permission = None;


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
    CF::Continue(controller.next_state(ExecRemovedGuard{}))
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

impl<'space, 'machine, S: Space> Controller<'machine, 'space, ExecRemovedGuard, S> {
    /// Drop the permission, move to [`PreTransform`] type state
    #[inline(always)]
    pub fn drop_permission(self) ->  Controller<'machine, 'space, PreTransform, S>{ drop_permission_impl(self) }

    /// skip explicitly dropping the permission (it is still implicitly dropped) and go directly to [`Controller<'machine,'state, PreTransform, S>::transform`]
    #[inline(always)]
    pub fn transform(self, at_critical_section : impl FnOnce(&Machine<'space, 'machine, S>)) -> Result<Controller<'machine, 'space, LoopStart, S>, TransformErr<'machine, 'space, S>,>
    {
        self.drop_permission().transform(at_critical_section)
    }
}

fn drop_permission_impl<'space, 'machine, S: Space>(controller : Controller<'machine, 'space, ExecRemovedGuard, S>) ->  Controller<'machine, 'space, PreTransform, S>
{
    let Machine { exec_permission, .. } = machine_mut!(controller);
    core::debug_assert!(exec_permission.is_some());
    *exec_permission = None;
    controller.next_state(PreTransform {})
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
    pub fn defer_guard(self) -> Result<Controller<'machine, 'space, DeferGuard, S>, (Self, S::PermissionErr)> { defer_guard_impl(self) }

    /// Adds retry logic to [`Self::defer_guard`];
    ///
    /// Retry logic should mirror [`Controller<'machine, 'space, LoopStart, S>::exec_permission_with_retries`].
    #[inline(always)]
    pub fn defer_guard_with_retries(mut self, max_retries : usize) -> Result<Controller<'machine, 'space, DeferGuard, S>, (Self, S::PermissionErr)>
    {
        let mut err = None;
        for _each in 0..max_retries.max(1) {
            match self.defer_guard() {
                Ok(ok)     => return Ok(ok),
                Err((c,e)) => { (self, err) = (c, Some(e))},
            };
            std::thread::sleep(core::time::Duration::from_micros(500));
        }
        Err((self, err.unwrap()))
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


    // we need an shared reference for the critical section
    let m_ref = machine_ref!(controller);
    core::debug_assert!( m_ref.pattern_templates.is_some() );
    let (patterns, templates) = unsafe { m_ref.pattern_templates.as_ref().unwrap_unchecked() };

    let (mut read_map, template_prefixes, mut writers) = match m_ref.space.acquire_transform_permissions(patterns, templates, m_ref.auth, ||at_critical_section(m_ref)) {
        Ok(ok)   => ok,
        Err(err) => return Err(TransformErr::Permission((controller, err))),
    };


    // We switch back to the mutable reference
    let Machine { space, prefix_len, buffer, retry_remaining, pattern_templates, steps_remaining, .. } = machine_mut!(controller);
    core::debug_assert!( pattern_templates.is_some() );
    let (patterns, templates) = unsafe { pattern_templates.as_ref().unwrap_unchecked() };

    //Insert the controller expression into the read_map
    read_map.set_val_at(unsafe { rt.span().as_ref().unwrap() }, ());

    space.transform_multi_multi(&patterns, &read_map, &templates, &template_prefixes, &mut writers);
 
    core::debug_assert!(*steps_remaining > 0);
    *steps_remaining -= 1;
    *pattern_templates = None;
    *retry_remaining = false;
    buffer.truncate(*prefix_len);

    Ok(controller.next_state(LoopStart{}))
}

fn defer_guard_impl <'space, 'machine, S: Space>(controller : Controller<'machine, 'space, PreTransform, S>) -> Result<Controller<'machine, 'space, DeferGuard, S>, (Controller<'machine, 'space, PreTransform, S>, S::PermissionErr)>
{
    let Machine { space, prefix_len, auth, buffer, exec_permission, pattern_templates, ..  } = machine_mut!(controller);
    // we are reusing this for a different permission
    core::debug_assert!(exec_permission.is_none());

    match space.new_writer(&buffer[..*prefix_len], auth) {
        Ok(writer) => {
                        *pattern_templates = None;
                        *exec_permission = Some(writer);
                        Ok(controller.next_state(DeferGuard {}))
                      },
        Err(err)   => Err((controller, err)),
    }
}

impl<'space, 'machine, S: Space> Controller<'machine, 'space, DeferGuard, S> {
    /// Reinsert the current exec, and drop the permission, moving back to [`LoopStart`].
    #[inline(always)]
    pub fn defer_current_exec(self) -> Controller<'machine, 'space, LoopStart, S> { defer_current_exec_impl(self) }
}

fn defer_current_exec_impl<'space, 'machine, S: Space>(controller : Controller<'machine, 'space, DeferGuard, S>) -> Controller<'machine, 'space, LoopStart, S> {
    let Machine { space, prefix_len, buffer, retry_remaining, exec_permission, ..  } = machine_mut!(controller);
    core::debug_assert!(exec_permission.is_some());
    let mut writer = unsafe { exec_permission.take().unwrap_unchecked() };

    let mut exec_wz = space.write_zipper(&mut writer);
    exec_wz.descend_to(&buffer[*prefix_len..]);
    exec_wz.set_val(());
    *retry_remaining = true;

    controller.next_state(LoopStart {})
}

impl<'machine, 'space, S : Space> MachineHandle<'machine, 'space, S> {
/// This gives the basic logic of metta_calculus via the [`MachineHandle`] with no retries, but tries to defer on a failed transform. Otherwise it bubbles up an error
pub fn advance(self) -> ControlFlow<Result<(), (Self, ExecError<S>)>, Self> {
    type MH<'m, 's, S> = MachineHandle<'m, 's, S>;
    ControlFlow::Continue(match self {
        MH::LoopStart            (controller) => match controller.exec_permission() {
                                                     Ok(ok)      => ok.to_handle(),
                                                     Err((c,e)) => {
                                                         let s = c.inspect_machine().space;
                                                         return ControlFlow::Break(Err((c.to_handle(), ExecError::perm_err(s, e))))
                                                     }
                                                 },
        MH::ExecRemovalPermission(controller) => if let CF::Continue(h) = controller.exec_lookup_to_handle() {h} else {return ControlFlow::Break(Ok(()));},
        MH::ExecRemovedGuard     (controller) => controller.drop_permission().to_handle(),
        MH::ExecsRemaining       (controller) => controller.continue_loop().to_handle(),
        MH::PreTransform         (controller) => match controller.transform(|_|{/* journal transform in critical section */}) {
                                                     Ok(ok)                                 => ok.to_handle(),
                                                     Err(TransformErr::Syntax((c,e)))       => return ControlFlow::Break(Err((c.to_handle(), ExecError::Syntax(e)))),
                                                     Err(TransformErr::Permission((c, _e))) => match c.defer_guard() {
                                                                                                   Ok(ok)     => ok.to_handle(),
                                                                                                   Err((c,e)) => {
                                                                                                       let s = c.inspect_machine().space;
                                                                                                       return ControlFlow::Break( Err((c.to_handle(), ExecError::perm_err(s, e))))
                                                                                                   }
                                                                                               },
                                                 },
        MH::DeferGuard           (controller) => controller.defer_current_exec().to_handle(), // journal deferal reinsertion
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
let mut start_controller = Machine::init(&mut machine, space, thread_id_sexpr_str, step_cnt, auth);

'process_execs : loop {
    let exec_permission = match start_controller.exec_permission_with_retries(max_retries) {
        Ok(ok)       => ok,
        Err((_c, e)) => return Err(ExecError::perm_err(space, e)),
    };

    let removed = match exec_permission.exec_lookup() {
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
        Ok(ok)                                => {
                                                    if step_cnt > 0 {
                                                        step_cnt -= 1
                                                    } else {
                                                        //Finished running the allotted number of steps
                                                        break 'process_execs Ok(())
                                                    }
                                                    ok
                                                 },
        Err(TransformErr::Syntax((_c,e)))      => return Err(ExecError::Syntax(e)),
        Err(TransformErr::Permission((c, _e))) => {
                                                    let defer_guard = match c.defer_guard_with_retries(max_retries) {
                                                        Ok(ok)      => ok,
                                                        Err((_c,e)) => return Err(ExecError::perm_err(space, e)),
                                                    };
                                                    // journal deferal reinsertion
                                                    defer_guard.defer_current_exec()
                                                  },
    };
}
}



/// The basic implementation using [`MachineHandle`] and including retry logic. comments show points one could include intermidiate actions like journaling
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
let mut handle = Machine::init(&mut machine, space, thread_id_sexpr_str, step_cnt, auth).to_handle();

'process_execs : loop {
    handle = match handle {
        MH::LoopStart            (controller) => match controller.exec_permission_with_retries(max_retries) {
                                                     Ok(ok)      => ok.to_handle(),
                                                     Err((_c,e)) => return Err(ExecError::perm_err(space, e)),
                                                 },
        MH::PreTransform         (controller) => match controller.transform(|_|{/* journal transform in critical section */}) {
                                                     Ok(ok)                                 => ok.to_handle(),
                                                     Err(TransformErr::Syntax((_c,e)))      => return Err(ExecError::Syntax(e)),
                                                     Err(TransformErr::Permission((c, _e))) => match c.defer_guard_with_retries(max_retries) {
                                                                                                   Ok(ok)      => ok.to_handle(),
                                                                                                   Err((_c,e)) => return Err(ExecError::perm_err(space, e)),
                                                                                               },
                                                 },
        otherwise => match otherwise.advance() {
            ControlFlow::Continue(c) => c,
            ControlFlow::Break(b)    => return b.map_err(|(_,e)|e),
        }
    };
}
}



// ///////////////////
// SEMANTIC MODEL //
// /////////////////
//
// A step countdown for sucessful iterations should be included
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

// this models the the behavior of the upper semantic model as closely as described
#[allow(unused)]
pub(crate) fn metta_calculus_model<'space, S: Space>(
space               : &'space S,
thread_id_sexpr_str : &str,
// adding a step counter was requested as an ammendment to the "semantic model"
mut step_cnt        : usize,
auth                : &S::Auth,
) -> Result<(), ExecError<S>> {
let mut machine = None;
let mut start_controller = Machine::init(&mut machine, space, thread_id_sexpr_str, step_cnt, auth);
const MAX_RETRIES : usize = usize::MAX;

'process_execs : loop {
    let exec_permission = match start_controller.exec_permission_with_retries(MAX_RETRIES) {
        Ok(ok)       => ok,
        Err((_c, e)) => panic!("Reached the end of the universe."),
    };

    let removed = match exec_permission.exec_lookup() {
        CF::Continue(removed)                                 => removed,
        CF::Break(LookupBaseCases::Done)                      => return Ok(()),
        CF::Break(LookupBaseCases::ExecsRemaining(remaining)) => {
                                                                   start_controller = remaining.continue_loop();
                                                                   continue 'process_execs;
                                                                 },
    };
    start_controller = match removed.transform(|_|{}) {
        Ok(ok)                                 => ok,
        Err(TransformErr::Syntax((_c,e)))      => return Err(ExecError::Syntax(e)),
        Err(TransformErr::Permission((c, _e))) => {
                                                    let defer_guard = match c.defer_guard_with_retries(MAX_RETRIES) {
                                                        Ok(ok)      => ok,
                                                        Err((_c,e)) => panic!("Reached the end of the universe."),
                                                    };
                                                    defer_guard.defer_current_exec()
                                                  },
    };
}
}
