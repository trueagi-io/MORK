theory RoutingSafe
  imports Main
begin

text \<open>
  The mathematical core of the routing condition in the unification-aware
  worst-case-optimal join.

  The leapfrog intersects join-key domains by EQUALITY on the canonical encoding.
  The reference unification-join intersects them by UNIFIABILITY. These two
  notions of agreement coincide exactly when the join keys are ground, which is
  the leapfrog-safe condition the router checks. When a join key is non-ground
  (a data variable reached a join position), unifiability is strictly weaker than
  equality, so the router must fall back to the per-tuple unifier.

  This theory proves that coincidence on ground terms and lifts it to the join.
\<close>

datatype ('f, 'x) trm = V 'x | F 'f "('f, 'x) trm list"

fun vars :: "('f, 'x) trm \<Rightarrow> 'x set" where
  "vars (V x) = {x}"
| "vars (F f ts) = \<Union> (set (map vars ts))"

definition ground :: "('f, 'x) trm \<Rightarrow> bool" where
  "ground t \<longleftrightarrow> vars t = {}"

fun appl :: "('x \<Rightarrow> ('f, 'x) trm) \<Rightarrow> ('f, 'x) trm \<Rightarrow> ('f, 'x) trm" where
  "appl s (V x) = s x"
| "appl s (F f ts) = F f (map (appl s) ts)"

text \<open>A substitution is the identity on a ground term.\<close>
lemma appl_ground:
  assumes "ground t"
  shows "appl s t = t"
  using assms
proof (induction t)
  case (V x)
  then show ?case by (simp add: ground_def)
next
  case (F f ts)
  have "appl s u = u" if "u \<in> set ts" for u
  proof -
    from F.prems that have "ground u" by (auto simp: ground_def)
    with F.IH that show ?thesis by blast
  qed
  then show ?case by (simp add: map_idI)
qed

definition unifiable :: "('f, 'x) trm \<Rightarrow> ('f, 'x) trm \<Rightarrow> bool" where
  "unifiable s t \<longleftrightarrow> (\<exists>\<sigma>. appl \<sigma> s = appl \<sigma> t)"

text \<open>Core: on ground terms, unifiability is exactly equality.\<close>
theorem ground_unifiable_iff_eq:
  assumes "ground s" and "ground t"
  shows "unifiable s t \<longleftrightarrow> s = t"
proof
  assume "unifiable s t"
  then obtain \<sigma> where "appl \<sigma> s = appl \<sigma> t"
    by (auto simp: unifiable_def)
  with appl_ground[OF assms(1)] appl_ground[OF assms(2)]
  show "s = t" by simp
next
  assume "s = t"
  then show "unifiable s t" by (auto simp: unifiable_def)
qed

text \<open>
  Lift to the join. A relation's join-key domain is a set of terms. The leapfrog
  keeps the equality-consistent pairs; the unification-join keeps the
  unifiable-consistent pairs. If every key in both domains is ground, the two
  results are identical. This is the leapfrog-safe guarantee.
\<close>
corollary leapfrog_safe_join_eq:
  assumes "\<And>s. s \<in> S \<Longrightarrow> ground s" and "\<And>t. t \<in> T \<Longrightarrow> ground t"
  shows "{(s, t) \<in> S \<times> T. unifiable s t} = {(s, t) \<in> S \<times> T. s = t}"
  using assms ground_unifiable_iff_eq by auto

text \<open>
  The boundary the router respects: when a key is NOT ground, unifiability is
  strictly weaker than equality, so the leapfrog would be unsound for the
  unification-join. A variable unifies with any constant but is not equal to it.
\<close>
lemma nonground_unifiable_strictly_weaker:
  "unifiable (V x) (F c [])" and "V x \<noteq> F c []"
proof -
  show "unifiable (V x) (F c [])"
    by (auto simp: unifiable_def intro!: exI[of _ "\<lambda>_. F c []"])
  show "V x \<noteq> F c []" by simp
qed

end
