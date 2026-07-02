theory TotalRouterSafe
  imports ZipperUnifySafe
begin

text \<open>
  The relaxed router sends EVERY relation-prefixed conjunction to the zipper join. The join's
  per-column step is no longer the byte-level union-find of ZipperUnifySafe, whose boundary
  (nonflat_uf_unsound) forced the old decline; it is full unification threaded through one
  bindings store, re-solved at each accepted column, with an assignment rejected when the answer
  emit cuts a cycle.

  Three facts carry that design. Pruning a branch whose equation prefix has no solution is sound,
  because a solution of a system solves every subsystem (solvable_mono). The columns cannot be
  decided independently, because pairwise unifiability does not imply a simultaneous solution
  (threading_necessary), which is why one bindings store threads through the whole descent. And
  the emit-time cycle rejection is exactly unsolvability: an equation binding a variable to a
  term properly containing it has no finite solution (occurs_unsolvable).
\<close>

definition solvable :: "(('f, 'x) trm \<times> ('f, 'x) trm) set \<Rightarrow> bool" where
  "solvable E \<longleftrightarrow> (\<exists>\<sigma>. \<forall>(s, t) \<in> E. appl \<sigma> s = appl \<sigma> t)"

text \<open>A solution of the system solves every subsystem: pruning on a failed prefix is sound.\<close>
lemma solvable_mono:
  assumes "solvable E" and "E' \<subseteq> E"
  shows "solvable E'"
  using assms unfolding solvable_def by blast

text \<open>Every equation of a solvable system is unifiable on its own.\<close>
lemma solvable_pointwise:
  assumes "solvable E" and "(s, t) \<in> E"
  shows "unifiable s t"
  using assms unfolding solvable_def unifiable_def by blast

text \<open>
  The converse fails: pairwise unifiability does not give a simultaneous solution, so a join
  testing each column against its candidate in isolation would be unsound. The bindings must
  thread.
\<close>
lemma threading_necessary:
  fixes f g :: 'f and x :: 'x
  assumes "f \<noteq> g"
  shows "unifiable (V x) (F f [])" and "unifiable (V x) (F g [])"
    and "\<not> solvable {(V x, F f []), (V x, F g [])}"
proof -
  show "unifiable (V x) (F f [])"
    by (auto simp: unifiable_def intro!: exI[of _ "\<lambda>_. F f []"])
  show "unifiable (V x) (F g [])"
    by (auto simp: unifiable_def intro!: exI[of _ "\<lambda>_. F g []"])
  show "\<not> solvable {(V x, F f []), (V x, F g [])}"
  proof
    assume "solvable {(V x, F f []), (V x, F g [])}"
    then have "\<exists>\<sigma>. appl \<sigma> (V x) = appl \<sigma> (F f [])
      \<and> appl \<sigma> (V x) = appl \<sigma> (F g [])"
      unfolding solvable_def by simp
    then obtain \<sigma> where "appl \<sigma> (V x) = appl \<sigma> (F f [])"
      and "appl \<sigma> (V x) = appl \<sigma> (F g [])"
      by blast
    then have "F f [] = F g []" by simp
    with assms show False by simp
  qed
qed

fun tsize :: "('f, 'x) trm \<Rightarrow> nat" where
  "tsize (V x) = 1"
| "tsize (F f ts) = 1 + sum_list (map tsize ts)"

text \<open>A variable's image is never larger than the image of a term containing the variable.\<close>
lemma tsize_appl_var_le:
  assumes "x \<in> vars t"
  shows "tsize (\<sigma> x) \<le> tsize (appl \<sigma> t)"
  using assms
proof (induction t)
  case (V y)
  then show ?case by simp
next
  case (F f ts)
  then obtain u where u: "u \<in> set ts" "x \<in> vars u" by auto
  with F.IH have "tsize (\<sigma> x) \<le> tsize (appl \<sigma> u)" by blast
  moreover have "tsize (appl \<sigma> u) \<le> sum_list (map tsize (map (appl \<sigma>) ts))"
    using u(1) by (intro member_le_sum_list) auto
  ultimately show ?case by simp
qed

text \<open>
  The occurs case: a variable equated with a term properly containing it has no finite solution.
  The join's emit records exactly this as a cut cycle and drops the row, so a cyclic assignment
  yields no answer, as whole-tuple unification demands.
\<close>
theorem occurs_unsolvable:
  assumes "x \<in> vars t" and "t \<noteq> V x"
  shows "\<not> unifiable (V x) t"
proof
  assume "unifiable (V x) t"
  then obtain \<sigma> where eq: "appl \<sigma> (V x) = appl \<sigma> t"
    by (auto simp: unifiable_def)
  from assms obtain f ts where t: "t = F f ts"
    by (cases t) auto
  from assms(1) t obtain u where u: "u \<in> set ts" "x \<in> vars u" by auto
  have "tsize (\<sigma> x) \<le> tsize (appl \<sigma> u)"
    using u(2) by (rule tsize_appl_var_le)
  also have "\<dots> \<le> sum_list (map tsize (map (appl \<sigma>) ts))"
    using u(1) by (intro member_le_sum_list) auto
  also have "\<dots> < tsize (appl \<sigma> (F f ts))" by simp
  finally have "tsize (\<sigma> x) < tsize (appl \<sigma> t)" using t by simp
  with eq show False by simp
qed

end
