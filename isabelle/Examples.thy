theory Examples
  imports Main_Results
begin

section \<open>Examples\<close>

subsection \<open>A criterion for divergence\<close>

lemma cd_fwd_sig_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  by (induction rule: rtranclp_induct) (auto intro: cd_fwd_sig)

text \<open>A term that returns to itself through a \<open>\<beta>\<^sub>v\<close>-step has no normal form.\<close>

lemma loop_not_CFN:
  assumes b: "M \<rightarrow>\<^sub>\<beta> M1" and s: "sig\<^sup>*\<^sup>* M1 M"
  shows "\<not> CFN M"
proof
  assume "CFN M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" by (auto simp: CFN_def)
  from steps_cd[OF r n] obtain k where c: "cd M k N" by blast
  from cd_fwd_beta[OF b c] obtain j where k: "k = Suc j" and c1: "cd M1 j N" by blast
  have c2: "cd M j N" by (rule cd_fwd_sig_steps[OF s c1])
  have "Suc j = j" using cd_det[OF c[unfolded k] c2] by (rule conjunct1)
  then show False by simp
qed

subsection \<open>Terms\<close>

definition dw :: trm where "dw = Lam 0 (App (Var 0) (Var 0))"
definition Omega :: trm where "Omega = App dw dw"
definition K :: trm where "K = Lam 0 (Lam 1 (Var 1))"

lemma Omega_loop: "Omega \<rightarrow>\<^sub>\<beta> Comp (App (Var 0) (Var 0)) (Extn dw 0 Id)"
  "sig\<^sup>*\<^sup>* (Comp (App (Var 0) (Var 0)) (Extn dw 0 Id)) Omega"
proof -
  have e: "Omega = App (Lam 0 (App (Var 0) (Var 0))) dw" by (simp add: Omega_def dw_def)
  show "Omega \<rightarrow>\<^sub>\<beta> Comp (App (Var 0) (Var 0)) (Extn dw 0 Id)"
    unfolding e by (rule Beta2) (simp add: dw_def FLam)
  let ?e = "Extn dw 0 Id"
  have 1: "Comp (App (Var 0) (Var 0)) ?e \<rightarrow>\<^sub>\<sigma> App (Comp (Var 0) ?e) (Comp (Var 0) ?e)"
    by (rule sig.DApp)
  have 2: "App (Comp (Var 0) ?e) (Comp (Var 0) ?e) \<rightarrow>\<^sub>\<sigma> App dw (Comp (Var 0) ?e)"
    by (rule sig.AppL[OF sig.VarRef])
  have 3: "App dw (Comp (Var 0) ?e) \<rightarrow>\<^sub>\<sigma> App dw dw"
    by (rule sig.AppR[OF sig.VarRef])
  show "sig\<^sup>*\<^sup>* (Comp (App (Var 0) (Var 0)) ?e) Omega"
    unfolding Omega_def using 1 2 3 by (meson converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
qed

theorem Omega_not_Typ: "\<not> Typ Omega"
  using loop_not_CFN[OF Omega_loop] main_characterization by blast

text \<open>
  The argument is evaluated first, so \<open>K \<Omega>\<close> diverges in call-by-value
  (in the call-by-name system it is typable).
\<close>

theorem K_Omega_not_Typ: "\<not> Typ (App K Omega)"
proof -
  have b: "App K Omega \<rightarrow>\<^sub>\<beta> App K (Comp (App (Var 0) (Var 0)) (Extn dw 0 Id))"
    by (rule AppR[OF _ Omega_loop(1)]) (simp add: K_def FLam)
  have s: "sig\<^sup>*\<^sup>* (App K (Comp (App (Var 0) (Var 0)) (Extn dw 0 Id))) (App K Omega)"
    by (rule sig_steps_lift[OF sig.AppR Omega_loop(2)])
  show ?thesis using loop_not_CFN[OF b s] main_characterization by blast
qed

text \<open>An abstraction is a value even if its body diverges.\<close>

theorem K_lam_Omega_Typ: "Typ (App K (Lam 2 Omega))"
proof -
  have b: "App K (Lam 2 Omega) \<rightarrow>\<^sub>\<beta> Comp (Lam 1 (Var 1)) (Extn (Lam 2 Omega) 0 Id)"
    unfolding K_def by (rule Beta2) (rule FLam)
  have "NF (Comp (Lam 1 (Var 1)) (Extn (Lam 2 Omega) 0 Id))"
  proof (rule fb_NF[OF FClo])
    show "sig_normal (Comp (Lam 1 (Var 1)) (Extn (Lam 2 Omega) 0 Id))"
      by (auto simp: normal_def Omega_def dw_def elim!: sig.cases)
  qed
  moreover have "App K (Lam 2 Omega) \<rightarrow>\<^sub>v\<^sup>* Comp (Lam 1 (Var 1)) (Extn (Lam 2 Omega) 0 Id)"
    using beta_imp_cbv[OF b] by (rule r_into_rtranclp)
  ultimately have "CFN (App K (Lam 2 Omega))" using FClo unfolding CFN_def by blast
  then show ?thesis using main_characterization by blast
qed

text \<open>Environments are lazy: a divergent component that is never looked up is harmless.\<close>

theorem lazy_env_Typ: "Typ (Comp (Var 1) (Extn Omega 0 (Extn (Var 2) 1 Id)))"
proof -
  have 1: "Comp (Var 1) (Extn Omega 0 (Extn (Var 2) 1 Id)) \<rightarrow>\<^sub>\<sigma> Comp (Var 1) (Extn (Var 2) 1 Id)"
    by (rule sig.VarSkip) simp
  have 2: "Comp (Var 1) (Extn (Var 2) 1 Id) \<rightarrow>\<^sub>\<sigma> Var 2" by (rule sig.VarRef)
  have "CFN (Comp (Var 1) (Extn Omega 0 (Extn (Var 2) 1 Id)))"
    unfolding CFN_def
    using 1 2 fb_Var NF_Var
    by (meson sig_imp_cbv converse_rtranclp_into_rtranclp rtranclp.rtrancl_refl)
  then show ?thesis using main_characterization by blast
qed

text \<open>Applying an environment is a clash.\<close>

theorem clash_example: "\<not> Typ (App Id Id)"
proof (rule clash_not_Typ)
  show "NF (App Id Id)" by (auto simp: normal_def cbv_def elim!: sig.cases beta.cases)
  show "\<not> fb (App Id Id)" by (simp add: fb_App_iff)
qed

end
