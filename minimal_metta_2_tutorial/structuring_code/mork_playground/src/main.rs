fn main() -> std::io::Result<()> {
   use std::io::Write;

   // //////////
   // CONFIG //
   // ////////
   let input_file_path     = concat!( env!("CARGO_MANIFEST_DIR"), "/Input.mm2" );
   let output_file_path    = concat!( env!("CARGO_MANIFEST_DIR"), "/Output.mm2");
   let trace_file_path     = concat!( env!("CARGO_MANIFEST_DIR"), "/Trace.mm2" );
   let steps               = 500;
   let execs_per_step      = 1.max(1);
   let do_trace            = true; // tracing happens once per iteration
   
   let (in_pattern,    in_template   ) = ("$", "_1"); // $x => $x
   let (out_pattern,   out_template  ) = ("$", "_1"); // $x => $x
   let (trace_pattern, trace_template) = ("$", "_1"); // $x => $x
   // let (trace_pattern, trace_template) = ("[4] exec $ $ $", "[4] exec _1 _2 _3"); // use this instead to trace what execs are awaiting
   
   
   // ///////////////
   // THE PROGRAM //
   // /////////////
   
   let     in_file    = std::fs::File::open(input_file_path)?; 
   let mut out_file   = std::fs::File::options().create(true).write(true).truncate(true).open(output_file_path)?;
   let mut trace_file = std::fs::File::options().create(true).write(true).truncate(true).open(trace_file_path)?;
   
   // initialize the space
   let mut s = mork::space::Space::new();
   
   // IMPORT
   let input = std::io::read_to_string(&in_file)?;
   s.add_sexpr(input.as_bytes(), mork::expr!(s,"$"), mork::expr!(s,"_1"));
   
   
   
   // run execs and traces
   let sys_time = || std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH);
   if do_trace {
      let mut scratch = Vec::new();
      let mut old = Vec::new();
   
      writeln!(trace_file, "; Begin Trace at time since UNIX_EPOCH : {:?}", sys_time())?;
      for each in 0..=steps{
         scratch.clear();
         s.dump_sexpr(mork::expr!(s, "$"), mork::expr!(s, "_1"), &mut scratch);
         if scratch.as_slice() == old.as_slice() {
            // reached a fix-point, no point tracing more
            break
         } else {
            (scratch, old) = (old, scratch)
         }
   
         writeln!(trace_file, "\n; Steps : {}, run execs : {}",each, each*execs_per_step)?;
         s.dump_sexpr(mork::expr!(s, trace_pattern), mork::expr!(s, trace_template), &mut trace_file);
      
         s.metta_calculus((execs_per_step-1));
      }
      writeln!(trace_file, "\n; Final State")?;
      s.dump_sexpr(mork::expr!(s, trace_pattern), mork::expr!(s, trace_template), &mut trace_file);
      writeln!(trace_file, "\n; End Trace at time since UNIX_EPOCH : {:?}\n", sys_time())?;
   } else {
      s.metta_calculus(steps*(execs_per_step-1));
   }
   
   // EXPORT
   writeln!(out_file, "; Output at time since UNIX_EPOCH : {:?}", sys_time())?;
   s.dump_sexpr(mork::expr!(s, out_pattern), mork::expr!(s, out_template), &mut out_file);
   writeln!(out_file, "; End Output\n")?;
   Ok(())
}
