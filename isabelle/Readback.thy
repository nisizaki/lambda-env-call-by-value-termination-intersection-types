theory Readback
  imports Main_Results Lambda
begin

section \<open>Readback into the \<open>\<lambda>\<close>-calculus: conservativity over open call-by-value\<close>

subsection \<open>Sorted (proper) terms\<close>

text \<open>
  \<open>tm\<close>: term-sorted, \<open>en\<close>: environment-sorted.  Environments are built from
  \<open>id\<close>, extensions and compositions; there are no environment variables.
  Pure \<open>\<lambda>\<close>-terms are term-sorted, and sortedness is preserved by \<open>\<rightarrow>\<^sub>v\<close>.
\<close>

fun tm :: "trm \<Rightarrow> bool" and en :: "trm \<Rightarrow> bool" where
  "tm (Var x) = True"
| "tm (Lam x M) = tm M"
| "tm (App M N) = (tm M \<and> tm N)"
| "tm (Comp M L) = (tm M \<and> en L)"
| "tm Id = False"
| "tm (Extn M x L) = False"
| "en (Var x) = False"
| "en (Lam x M) = False"
| "en (App M N) = False"
| "en (Comp L1 L2) = (en L1 \<and> en L2)"
| "en Id = True"
| "en (Extn M x L) = (tm M \<and> en L)"

fun pure :: "trm \<Rightarrow> bool" where
  "pure (Var x) = True"
| "pure (Lam x M) = pure M"
| "pure (App M N) = (pure M \<and> pure N)"
| "pure _ = False"

lemma pure_tm: "pure M \<Longrightarrow> tm M"
  by (induction M) auto

subsection \<open>Readback\<close>

text \<open>\<open>junk\<close> is used for ill-sorted positions; it is closed, so substitution fixes it.\<close>

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Id \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Id \<rho> = \<rho>"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Id
  then show ?case by simp
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

subsection \<open>Simulation\<close>

lemma sig_sorted:
  "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow>
     (tm M \<longrightarrow> tm N \<and> (\<forall>\<rho>. rb N \<rho> = rb M \<rho>)) \<and>
     (en M \<longrightarrow> en N \<and> (\<forall>\<rho>. rbe N \<rho> = rbe M \<rho>))"
  by (induction rule: sig.induct) (auto simp: fun_upd_def)

lemma beta_not_en: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> \<not> en M"
  by (induction rule: beta.induct) auto

lemma inert_not_en: "inert M \<Longrightarrow> \<not> en M"
  by (cases rule: inert.cases) auto

lemma fb_rb: "tm M \<Longrightarrow> (inert M \<longrightarrow> dinert (rb M DVar)) \<and> (fb M \<longrightarrow> dfb (rb M DVar))"
proof (induction M)
  case (Var x)
  then show ?case by (auto intro: dinert_dfb.intros)
next
  case (Lam x M)
  then show ?case by (auto intro: dinert_dfb.intros)
next
  case (App M1 M2)
  then show ?case
    by (auto simp: inert_App_iff fb_App_iff dinert_DApp_iff intro: dinert_dfb.intros)
next
  case Id then show ?case by simp
next
  case (Extn M1 x M2) then show ?case by simp
next
  case (Comp M1 M2)
  have i: "\<not> inert (Comp M1 M2)"
  proof
    assume "inert (Comp M1 M2)"
    then obtain x where "M1 = Var x" "inert M2" by (auto elim: inert.cases)
    then show False using Comp.prems inert_not_en by simp
  qed
  moreover have "dfb (rb (Comp M1 M2) DVar)" if "fb (Comp M1 M2)"
    using that
  proof (cases rule: fb_cases)
    case inert then show ?thesis using i by simp
  next
    case (clo x B L) then show ?thesis by (simp add: dinert_dfb.intros)
  qed auto
  ultimately show ?case by blast
qed

lemma beta_sorted:
  "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> rb M DVar \<rightarrow>\<^sub>f rb N DVar"
proof (induction rule: beta.induct)
  case (Beta1 N x M L)
  have f: "dfb (rb N DVar)" using fb_rb Beta1 by simp
  have "rb (App (Comp (Lam x M) L) N) DVar \<rightarrow>\<^sub>f rb (Comp M (Extn N x L)) DVar"
    using vbeta[OF f, of "rb M ((\<lambda>y. lift (rbe L DVar y) 0)(x := DVar 0))"]
    by (simp add: beta_rb)
  then show ?case using Beta1 by simp
next
  case (Beta2 N x M)
  have f: "dfb (rb N DVar)" using fb_rb Beta2 by simp
  have eq: "(rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0)))[rb N DVar/0] = rb M (DVar(x := rb N DVar))"
    by (rule beta_rb)
  have "DApp (DAbs (rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0)))) (rb N DVar) \<rightarrow>\<^sub>f
      rb M (DVar(x := rb N DVar))"
    using vbeta[OF f, of "rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0))"] eq by metis
  then have "rb (App (Lam x M) N) DVar \<rightarrow>\<^sub>f rb (Comp M (Extn N x Id)) DVar"
    by simp
  then show ?case using Beta2 by simp
next
  case (AppL M N L)
  then show ?case by (auto intro: vappL)
next
  case (AppR L M N)
  have "dfb (rb L DVar)" using fb_rb AppR by simp
  then show ?case using AppR by (auto intro: vappR)
next
  case (VarR M N x)
  then show ?case using beta_not_en by auto
qed

lemma cbv_sorted:
  assumes "M \<rightarrow>\<^sub>v N" "tm M"
  shows "tm N \<and> (rb N DVar = rb M DVar \<and> tlength N < tlength M \<or> rb M DVar \<rightarrow>\<^sub>f rb N DVar)"
  using assms sig_sorted beta_sorted sig_tlength_decrease by (auto simp: cbv_def)

lemma cbv_steps_sorted:
  "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> vred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
proof (induction rule: rtranclp_induct)
  case base then show ?case by simp
next
  case (step N P)
  then show ?case using cbv_sorted[of N P] by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed

subsection \<open>Sorted normal forms are fireballs (no clash)\<close>

lemma NF_AppL: "NF (App M N) \<Longrightarrow> NF M"
  by (auto simp: normal_def dest: cbv_AppL)

lemma NF_AppR: "NF (App M N) \<Longrightarrow> fb M \<Longrightarrow> NF N"
  by (auto simp: normal_def cbv_def intro: sig.AppR beta.AppR)

lemma NF_CompR_Var: "NF (Comp (Var x) N) \<Longrightarrow> NF N"
  by (auto simp: normal_def dest: cbv_VarR)

lemma sorted_NF_fb: "(tm M \<longrightarrow> NF M \<longrightarrow> fb M) \<and> (en M \<longrightarrow> NF M \<longrightarrow> fb M)"
proof (induction M)
  case (Var x) then show ?case by simp
next
  case (Lam x M) then show ?case by (simp add: FLam)
next
  case Id then show ?case by (simp add: FId)
next
  case (Extn M1 x M2) then show ?case by (simp add: FExtn)
next
  case (App M1 M2)
  have "fb (App M1 M2)" if t: "tm (App M1 M2)" and n: "NF (App M1 M2)"
  proof -
    have n1: "NF M1" using NF_AppL[OF n] .
    have f1: "fb M1" using App.IH(1) t n1 by simp
    have n2: "NF M2" using NF_AppR[OF n f1] .
    have f2: "fb M2" using App.IH(2) t n2 by simp
    from f1 show ?thesis
    proof (cases rule: fb_cases)
      case inert then show ?thesis using f2 by (simp add: fb_App_iff)
    next
      case (lam x B)
      then have "App M1 M2 \<rightarrow>\<^sub>v Comp B (Extn M2 x Id)" using f2 by (simp add: beta_imp_cbv Beta2)
      then show ?thesis using n by (auto simp: normal_def)
    next
      case (clo x B L)
      then have "App M1 M2 \<rightarrow>\<^sub>v Comp B (Extn M2 x L)" using f2 by (simp add: beta_imp_cbv Beta1)
      then show ?thesis using n by (auto simp: normal_def)
    qed (use t in auto)
  qed
  then show ?case by simp
next
  case (Comp M1 M2)
  have r: "\<not> Comp M1 M2 \<rightarrow>\<^sub>\<sigma> P" if "NF (Comp M1 M2)" for P
    using that by (auto simp: normal_def cbv_def)
  have e: "\<not> NF (Comp M1 M2)" if "en M1"
  proof
    assume n: "NF (Comp M1 M2)"
    show False
    proof (cases M1)
      case Id then show False using r[OF n] sig.IdL by blast
    next
      case (Extn P y Q) then show False using r[OF n] sig.DExtn by blast
    next
      case (Comp P Q) then show False using r[OF n] sig.Ass by blast
    qed (use that in auto)
  qed
  have "fb (Comp M1 M2)" if t: "tm (Comp M1 M2)" and n: "NF (Comp M1 M2)"
  proof (cases M1)
    case (Var x)
    have n2: "NF M2" using NF_CompR_Var n Var by simp
    have f2: "fb M2" using Comp.IH(2) t n2 by simp
    have en2: "en M2" using t by simp
    from f2 show ?thesis
    proof (cases rule: fb_cases)
      case inert then show ?thesis using en2 inert_not_en by blast
    next
      case id then show ?thesis using r[OF n] sig.IdR by blast
    next
      case (extn P y Q)
      show ?thesis
      proof (cases "y = x")
        case True then show ?thesis using r[OF n] sig.VarRef Var extn by blast
      next
        case False then show ?thesis using r[OF n] sig.VarSkip[OF False] Var extn by blast
      qed
    qed (use en2 in auto)
  next
    case (Lam x B) then show ?thesis by (simp add: FClo)
  next
    case (App P Q) then show ?thesis using r[OF n] sig.DApp by blast
  next
    case Id then show ?thesis using r[OF n] sig.IdL by blast
  next
    case (Extn P y Q) then show ?thesis using r[OF n] sig.DExtn by blast
  next
    case (Comp P Q) then show ?thesis using r[OF n] sig.Ass by blast
  qed
  moreover have "en (Comp M1 M2) \<Longrightarrow> NF (Comp M1 M2) \<Longrightarrow> fb (Comp M1 M2)" using e by simp
  ultimately show ?case by blast
qed

subsection \<open>Conservativity\<close>

lemma CFN_imp_lam_VN:
  assumes t: "tm M" and c: "CFN M"
  shows "lam_VN (rb M DVar)"
proof -
  obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and f: "fb N" using c by (auto simp: CFN_def)
  from cbv_steps_sorted[OF r t] have tN: "tm N" and h: "vred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
    by blast+
  have "dfb (rb N DVar)" using fb_rb tN f by blast
  then have "normal vred (rb N DVar)" using dfb_normal by blast
  then show ?thesis unfolding lam_VN_def using h by blast
qed

lemma vdist_imp_SN: "vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
  proof -
    fix M
    show "vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>v N"
        from cbv_sorted[OF s \<open>tm M\<close>] have tN: "tm N"
          and c: "rb N DVar = rb M DVar \<and> tlength N < tlength M \<or> rb M DVar \<rightarrow>\<^sub>f rb N DVar"
          by blast+
        from c show "SN_at cbv N"
        proof
          assume a: "rb N DVar = rb M DVar \<and> tlength N < tlength M"
          then have "vdist (rb N DVar) n" using less.prems(1) by simp
          then show ?thesis using less.hyps a tN by blast
        next
          assume "rb M DVar \<rightarrow>\<^sub>f rb N DVar"
          then obtain m where "n = Suc m" "vdist (rb N DVar) m"
            using vdist_step less.prems(1) by blast
          then show ?thesis using IHn tN by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma lam_VN_imp_CFSN: "tm M \<Longrightarrow> lam_VN (rb M DVar) \<Longrightarrow> CFSN M"
proof -
  assume t: "tm M" and w: "lam_VN (rb M DVar)"
  then obtain n where "vdist (rb M DVar) n" using lam_VN_vdist by blast
  then have "SN_at cbv M" using t vdist_imp_SN by blast
  moreover have "fb N" if r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" for N
  proof -
    have "tm N" using cbv_steps_sorted[OF r t] by blast
    then show ?thesis using sorted_NF_fb n by blast
  qed
  ultimately show ?thesis by (auto simp: CFSN_def)
qed

theorem conservativity_sorted:
  assumes "tm M"
  shows "(lam_VN (rb M DVar) \<longleftrightarrow> CFN M) \<and> (CFN M \<longleftrightarrow> CFSN M) \<and> (Typ M \<longleftrightarrow> CFN M)"
  using assms CFN_imp_lam_VN lam_VN_imp_CFSN CFSN_imp_CFN main_characterization by blast

theorem conservativity:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> lam_VN (rb M DVar)"
    and "lam_VN (rb M DVar) \<longleftrightarrow> CFSN M"
  using conservativity_sorted[OF pure_tm[OF assms]] CFN_iff_CFSN by blast+

end
