theory Main_Results
  imports Soundness
begin

section \<open>Main results\<close>

text \<open>
  Typability characterizes call-by-value normalization, and equivalently
  call-by-value termination: every reduction sequence is finite and ends in a
  clash-free normal form (a fireball).
\<close>

theorem main_characterization: "Typ M \<longleftrightarrow> CFN M"
  using soundness completeness by blast

theorem main_characterization_SN: "Typ M \<longleftrightarrow> CFSN M"
  using main_characterization CFN_iff_CFSN by blast

theorem Typ_imp_SN: "Typ M \<Longrightarrow> SN_at cbv M"
  using main_characterization_SN by (simp add: CFSN_def)

corollary clash_not_Typ: "NF M \<Longrightarrow> \<not> fb M \<Longrightarrow> \<not> Typ M"
proof
  assume n: "NF M" and c: "\<not> fb M" and "Typ M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and f: "fb N" using soundness by (auto simp: CFN_def)
  from normal_rtranclp[OF n r] f c show False by simp
qed

end
