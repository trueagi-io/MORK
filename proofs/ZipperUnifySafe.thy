theory ZipperUnifySafe
  imports RoutingSafe
begin

text \<open>
  Soundness of the zipper-native join's unifier.

  The zipper join intersects join keys with a trail UNION-FIND over the byte
  encoding, not a structural unifier. It treats a ground subterm, a complete
  self-delimiting byte span including a ground compound, as an opaque value
  compared by equality, and a stored variable as unifiable with anything. It
  never recurses into compound structure.

  That is sound exactly in the routing scope the gate enforces: no non-ground
  compound appears on either side. A term with no non-ground compound is FLAT,
  every functor node is ground, so the term is either a single variable or a
  fully ground term. On flat terms structural unifiability coincides with the
  union-find decision (either side is a variable, or the two are equal). This
  theory proves that coincidence and lifts it to the join intersection.
\<close>

definition flat :: "('f, 'x) trm \<Rightarrow> bool" where
  "flat t \<longleftrightarrow> (\<exists>x. t = V x) \<or> ground t"

text \<open>The decision the byte-level union-find environment makes for two keys.\<close>
definition uf_agree :: "('f, 'x) trm \<Rightarrow> ('f, 'x) trm \<Rightarrow> bool" where
  "uf_agree s t \<longleftrightarrow> (\<exists>x. s = V x) \<or> (\<exists>y. t = V y) \<or> s = t"

text \<open>On flat terms, structural unifiability is exactly the union-find decision.\<close>
theorem flat_unifiable_iff_uf_agree:
  assumes "flat s" and "flat t"
  shows "unifiable s t \<longleftrightarrow> uf_agree s t"
proof
  assume "unifiable s t"
  show "uf_agree s t"
  proof (cases "(\<exists>x. s = V x) \<or> (\<exists>y. t = V y)")
    case True
    then show ?thesis unfolding uf_agree_def by blast
  next
    case False
    then have "ground s" and "ground t" using assms by (auto simp: flat_def)
    with \<open>unifiable s t\<close> have "s = t" by (simp add: ground_unifiable_iff_eq)
    then show ?thesis unfolding uf_agree_def by blast
  qed
next
  assume "uf_agree s t"
  then consider (sv) "\<exists>x. s = V x" | (tv) "\<exists>y. t = V y" | (eq) "s = t"
    by (auto simp: uf_agree_def)
  then show "unifiable s t"
  proof cases
    case sv
    then obtain x where "s = V x" by blast
    have "appl (\<lambda>_. t) s = t" using \<open>s = V x\<close> by simp
    moreover have "appl (\<lambda>_. t) t = t"
    proof (cases "\<exists>y. t = V y")
      case True
      then obtain y where "t = V y" by blast
      then show ?thesis by simp
    next
      case False
      with assms(2) have "ground t" by (simp add: flat_def)
      then show ?thesis by (rule appl_ground)
    qed
    ultimately have "appl (\<lambda>_. t) s = appl (\<lambda>_. t) t" by simp
    then show ?thesis by (auto simp: unifiable_def)
  next
    case tv
    then obtain y where "t = V y" by blast
    have "appl (\<lambda>_. s) t = s" using \<open>t = V y\<close> by simp
    moreover have "appl (\<lambda>_. s) s = s"
    proof (cases "\<exists>x. s = V x")
      case True
      then obtain x where "s = V x" by blast
      then show ?thesis by simp
    next
      case False
      with assms(1) have "ground s" by (simp add: flat_def)
      then show ?thesis by (rule appl_ground)
    qed
    ultimately have "appl (\<lambda>_. s) s = appl (\<lambda>_. s) t" by simp
    then show ?thesis by (auto simp: unifiable_def)
  next
    case eq
    then show ?thesis by (auto simp: unifiable_def)
  qed
qed

text \<open>
  Lift to the join. A relation's join-key domain is a set of terms. The zipper
  join keeps the union-find-consistent pairs; the structural unification join
  keeps the unifiable pairs. If every key in both domains is flat, the two
  results are identical, so the byte-level union-find loses nothing the
  structural unifier finds, and finds nothing it does not.
\<close>
corollary zipper_uf_join_eq_unification_join:
  assumes "\<And>s. s \<in> S \<Longrightarrow> flat s" and "\<And>t. t \<in> T \<Longrightarrow> flat t"
  shows "{(s, t) \<in> S \<times> T. uf_agree s t} = {(s, t) \<in> S \<times> T. unifiable s t}"
  using assms flat_unifiable_iff_uf_agree by blast

text \<open>
  The boundary, exactly the routing gate: a non-ground compound is not flat, and
  there the union-find decision is unsound. The variable y inside the compound
  F g [V y] makes F f [F g [V y]] unifiable with F f [F g [F c []]] (substitute
  y := c) though they are not equal and neither is a variable, so uf_agree would
  wrongly reject the pair. This is why the gate declines non-ground compounds.
\<close>
lemma nonflat_uf_unsound:
  fixes f g c :: 'f and y :: 'x
  shows "unifiable (F f [F g [V y]]) (F f [F g [F c []]])"
    and "\<not> uf_agree (F f [F g [V y]]) (F f [F g [F c []]])"
    and "\<not> flat (F f [F g [V y]])"
proof -
  let ?s = "F f [F g [V y]]"
  let ?t = "F f [F g [F c []]]"
  show "unifiable ?s ?t"
    by (auto simp: unifiable_def intro!: exI[of _ "\<lambda>_. F c []"])
  show "\<not> uf_agree ?s ?t" by (simp add: uf_agree_def)
  show "\<not> flat ?s" by (simp add: flat_def ground_def)
qed

end
