theory Classical
  imports VTypes Readback
begin

section \<open>Agreement with a classical call-by-value intersection-type system\<close>

text \<open>
  For pure terms, \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> typability agrees with typability of the
  readback in the classical system of \<open>VTypes\<close>.  Both characterize
  normalizability of the readback in Open CBV (\<open>conservativity\<close> and
  \<open>classical_VN\<close>); the agreement is obtained through this common
  characterization, not by a syntactic translation of derivations.
\<close>

theorem classical_agreement:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> (\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>v rb M DVar : A)"
  using conservativity(1)[OF assms] classical_VN by blast

end
