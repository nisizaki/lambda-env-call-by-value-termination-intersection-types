theory Order_Independence
  imports Main_Results
begin

section \<open>Independence of the evaluation order\<close>

text \<open>
  \<open>\<beta>\<^sub>n\<close> is \<open>\<beta>\<^sub>v\<close> without the left-to-right restriction: an argument may be
  evaluated before the function part.  We show that typability also characterizes
  termination of \<open>\<sigma> \<union> \<beta>\<^sub>n\<close>: every reduction sequence, in any order, is finite and
  ends in a fireball.
\<close>

inductive betan :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>n" 50) where
  Beta1: "fb N \<Longrightarrow> App (Comp (Lam x M) L) N \<rightarrow>\<^sub>n Comp M (Extn N x L)"
| Beta2: "fb N \<Longrightarrow> App (Lam x M) N \<rightarrow>\<^sub>n Comp M (Extn N x Id)"
| AppL: "M \<rightarrow>\<^sub>n N \<Longrightarrow> App M L \<rightarrow>\<^sub>n App N L"
| AppR: "M \<rightarrow>\<^sub>n N \<Longrightarrow> App L M \<rightarrow>\<^sub>n App L N"
| VarR: "M \<rightarrow>\<^sub>n N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>n Comp (Var x) N"

definition cbvn :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "cbvn M N \<longleftrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<or> M \<rightarrow>\<^sub>n N"

definition CFSNn :: "trm \<Rightarrow> bool" where
  "CFSNn M \<longleftrightarrow> SN_at cbvn M \<and> (\<forall>N. cbvn\<^sup>*\<^sup>* M N \<longrightarrow> normal cbvn N \<longrightarrow> fb N)"

lemma beta_imp_betan: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> M \<rightarrow>\<^sub>n N"
  by (induction rule: beta.induct) (auto intro: betan.intros)

lemma cbv_imp_cbvn: "M \<rightarrow>\<^sub>v N \<Longrightarrow> cbvn M N"
  by (auto simp: cbv_def cbvn_def dest: beta_imp_betan)

lemma normal_cbvn_NF: "normal cbvn N \<Longrightarrow> NF N"
  by (auto simp: normal_def dest: cbv_imp_cbvn)

lemma inert_fb_no_betan:
  "(inert M \<longrightarrow> (\<forall>N. \<not> M \<rightarrow>\<^sub>n N)) \<and> (fb M \<longrightarrow> (\<forall>N. \<not> M \<rightarrow>\<^sub>n N))"
proof (induction M)
  case (App M1 M2)
  have i: "\<not> App M1 M2 \<rightarrow>\<^sub>n N" if "inert (App M1 M2)" for N
  proof
    assume b: "App M1 M2 \<rightarrow>\<^sub>n N"
    from that have a: "inert M1" "fb M2" by (simp_all add: inert_App_iff)
    from b show False
    proof (cases rule: betan.cases)
      case (Beta1 x M L) then show False using a by simp
    next
      case (Beta2 x M) then show False using a by simp
    next
      case (AppL N') then show False using App.IH(1) a by blast
    next
      case (AppR N') then show False using App.IH(2) a by blast
    qed
  qed
  then show ?case by (auto simp: fb_App_iff inert_App_iff)
next
  case (Comp M1 M2)
  have i: "\<not> Comp M1 M2 \<rightarrow>\<^sub>n N" if "inert (Comp M1 M2)" for N
  proof
    assume b: "Comp M1 M2 \<rightarrow>\<^sub>n N"
    from that obtain x where "M1 = Var x" and m2: "inert M2" by (auto elim: inert.cases)
    from b show False
    proof (cases rule: betan.cases)
      case (VarR N') then show False using Comp.IH(2) m2 by blast
    qed
  qed
  have "\<not> Comp M1 M2 \<rightarrow>\<^sub>n N" if "fb (Comp M1 M2)" for N
    using that
  proof (cases rule: fb_cases)
    case inert then show ?thesis using i by blast
  next
    case (clo x B L) then show ?thesis by (auto elim: betan.cases)
  qed auto
  then show ?case using i by blast
qed (auto elim: betan.cases)

lemma fb_no_betan: "fb M \<Longrightarrow> \<not> M \<rightarrow>\<^sub>n N"
  using inert_fb_no_betan by blast

subsection \<open>Commutation with \<open>\<sigma>\<close>\<close>

lemma betan_sig_commute: "M \<rightarrow>\<^sub>n M2 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> M1 \<Longrightarrow> \<exists>M3. M1 \<rightarrow>\<^sub>n M3 \<and> sig\<^sup>*\<^sup>* M2 M3"
proof (induction arbitrary: M1 rule: betan.induct)
  case (Beta1 N x B K)
  from Beta1.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    from Clo_sig_inv[OF AppL(2)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam x B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using AppL Beta1.hyps by (auto intro!: betan.Beta1 ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam x B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using AppL Beta1.hyps by (auto intro!: betan.Beta1 ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam x B"
      then show ?thesis using AppL Beta1.hyps by (auto intro!: betan.Beta2)
    qed
  next
    case (AppR N')
    have "fb N'" using sig_fb[OF Beta1.hyps AppR(2)] .
    then show ?thesis using AppR by (auto intro!: betan.Beta1 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (Beta2 N x B)
  from Beta2.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    then obtain B' where "P = Lam x B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using AppL Beta2.hyps by (auto intro!: betan.Beta2 ss1 sig.CompL)
  next
    case (AppR N')
    have "fb N'" using sig_fb[OF Beta2.hyps AppR(2)] .
    then show ?thesis using AppR by (auto intro!: betan.Beta2 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL M1a)
    from AppL.IH[OF AppL(2)] obtain M3 where "M1a \<rightarrow>\<^sub>n M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using AppL(1)
      by (auto intro!: betan.AppL sig_steps_lift[of "\<lambda>P. App P L"] sig.AppL)
  next
    case (AppR L')
    then show ?thesis using AppL.hyps by (auto intro!: betan.AppL ss1 sig.AppR)
  qed
next
  case (AppR M M' L)
  from AppR.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL L')
    then show ?thesis using AppR.hyps by (auto intro!: betan.AppR ss1 sig.AppL)
  next
    case (AppR M1a)
    from AppR.IH[OF AppR(2)] obtain M3 where "M1a \<rightarrow>\<^sub>n M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using AppR(1)
      by (auto intro!: betan.AppR sig_steps_lift[of "\<lambda>P. App L P"] sig.AppR)
  qed
next
  case (VarR M M' x)
  from VarR.prems show ?case
  proof (cases rule: sig.cases)
    case (CompR M1a)
    from VarR.IH[OF CompR(2)] obtain M3 where "M1a \<rightarrow>\<^sub>n M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using CompR(1)
      by (auto intro!: betan.VarR sig_steps_lift[of "\<lambda>P. Comp (Var x) P"] sig.CompR)
  qed (use VarR.hyps in \<open>auto elim: sig.cases betan.cases\<close>)
qed

lemma snf_betan: "M \<rightarrow>\<^sub>n M' \<Longrightarrow> \<exists>M3. snf M \<rightarrow>\<^sub>n M3 \<and> sig\<^sup>*\<^sup>* M' M3"
proof (induction "tlength M" arbitrary: M M' rule: less_induct)
  case less
  show ?case
  proof (cases "sig_normal M")
    case True
    then have "snf M = M" using snf_unique by blast
    then show ?thesis using less.prems by auto
  next
    case False
    then obtain M1 where s: "M \<rightarrow>\<^sub>\<sigma> M1" by (auto simp: normal_def)
    from betan_sig_commute[OF less.prems s] obtain M3' where
      a: "M1 \<rightarrow>\<^sub>n M3'" "sig\<^sup>*\<^sup>* M' M3'" by blast
    have lt: "tlength M1 < tlength M" using sig_tlength_decrease[OF s] .
    from less.hyps[OF lt a(1)] obtain M3 where b: "snf M1 \<rightarrow>\<^sub>n M3" "sig\<^sup>*\<^sup>* M3' M3"
      by blast
    have "snf M1 = snf M" using snf_steps[OF ss1[OF s]] .
    then show ?thesis using b a(2) by (metis rtranclp_trans)
  qed
qed

subsection \<open>Diamond with the left-to-right step\<close>

lemma Lam_no_betan: "Lam x M \<rightarrow>\<^sub>n N \<Longrightarrow> False" by (auto elim: betan.cases)
lemma Clo_no_betan: "Comp (Lam x M) L \<rightarrow>\<^sub>n N \<Longrightarrow> False" by (auto elim: betan.cases)

lemma diamond:
  "M \<rightarrow>\<^sub>n M' \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> M1 \<Longrightarrow> M' = M1 \<or> (\<exists>M12. M1 \<rightarrow>\<^sub>n M12 \<and> M' \<rightarrow>\<^sub>\<beta> M12)"
proof (induction arbitrary: M1 rule: betan.induct)
  case (Beta1 N x B L)
  from Beta1.prems show ?case
  proof (cases rule: beta.cases)
    case (AppL P) then show ?thesis using Clo_no_beta by blast
  next
    case (AppR P) then show ?thesis using fb_no_beta[OF Beta1.hyps] by blast
  qed simp_all
next
  case (Beta2 N x B)
  from Beta2.prems show ?case
  proof (cases rule: beta.cases)
    case (AppL P) then show ?thesis using Lam_no_beta by blast
  next
    case (AppR P) then show ?thesis using fb_no_beta[OF Beta2.hyps] by blast
  qed simp_all
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: beta.cases)
    case (Beta1 x B K) then show ?thesis using AppL.hyps Clo_no_betan by blast
  next
    case (Beta2 x B) then show ?thesis using AppL.hyps Lam_no_betan by blast
  next
    case (AppL P)
    from AppL.IH[OF AppL(2)] show ?thesis
    proof
      assume "M' = P" then show ?thesis using AppL by simp
    next
      assume "\<exists>M12. P \<rightarrow>\<^sub>n M12 \<and> M' \<rightarrow>\<^sub>\<beta> M12"
      then obtain M12 where "P \<rightarrow>\<^sub>n M12" "M' \<rightarrow>\<^sub>\<beta> M12" by blast
      then show ?thesis using AppL by (blast intro: betan.AppL beta.AppL)
    qed
  next
    case (AppR P) then show ?thesis using AppL.hyps fb_no_betan by blast
  qed
next
  case (AppR M M' L)
  from AppR.prems show ?case
  proof (cases rule: beta.cases)
    case (Beta1 x B K) then show ?thesis using AppR.hyps fb_no_betan by blast
  next
    case (Beta2 x B) then show ?thesis using AppR.hyps fb_no_betan by blast
  next
    case (AppL P)
    then have "App P M \<rightarrow>\<^sub>n App P M'" "App L M' \<rightarrow>\<^sub>\<beta> App P M'"
      using AppR.hyps by (auto intro: betan.AppR beta.AppL)
    then show ?thesis using AppL by blast
  next
    case (AppR P)
    from AppR.IH[OF AppR(3)] show ?thesis
    proof
      assume "M' = P" then show ?thesis using AppR by simp
    next
      assume "\<exists>M12. P \<rightarrow>\<^sub>n M12 \<and> M' \<rightarrow>\<^sub>\<beta> M12"
      then obtain M12 where "P \<rightarrow>\<^sub>n M12" "M' \<rightarrow>\<^sub>\<beta> M12" by blast
      then show ?thesis using AppR by (blast intro: betan.AppR beta.AppR)
    qed
  qed
next
  case (VarR M M' x)
  from VarR.prems show ?case
  proof (cases rule: beta.cases)
    case (VarR P)
    from VarR.IH[OF VarR(2)] show ?thesis
    proof
      assume "M' = P" then show ?thesis using VarR by simp
    next
      assume "\<exists>M12. P \<rightarrow>\<^sub>n M12 \<and> M' \<rightarrow>\<^sub>\<beta> M12"
      then obtain M12 where "P \<rightarrow>\<^sub>n M12" "M' \<rightarrow>\<^sub>\<beta> M12" by blast
      then show ?thesis using VarR by (blast intro: betan.VarR beta.VarR)
    qed
  qed
qed

subsection \<open>Every \<open>\<beta>\<^sub>n\<close>-step shortens the deterministic chain\<close>

lemma cd_fwd_sig_steps': "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  by (induction rule: rtranclp_induct) (auto intro: cd_fwd_sig)

lemma cd_back_sig_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M n E"
  by (induction rule: converse_rtranclp_induct) (auto intro: cd_back_sig)

lemma cd_snf_self: "cd M n E \<Longrightarrow> cd (snf M) n E"
  using cd_fwd_sig_steps' snf_spec by blast

lemma cd_betan:
  "cd M n E \<Longrightarrow> fb E \<Longrightarrow> M \<rightarrow>\<^sub>n M' \<Longrightarrow> \<exists>m < n. cd M' m E"
proof (induction n arbitrary: M M' rule: less_induct)
  case (less n)
  from snf_betan[OF less.prems(3)] obtain M3 where b: "snf M \<rightarrow>\<^sub>n M3" and s: "sig\<^sup>*\<^sup>* M' M3"
    by blast
  from less.prems(1) show ?case
  proof (cases rule: cd.cases)
    case cd0
    then have "fb (snf M)" using less.prems(2) by simp
    then show ?thesis using b fb_no_betan by blast
  next
    case (cdS N1 k)
    note d = diamond[OF b cdS(2)]
    from d show ?thesis
    proof
      assume "M3 = N1"
      then have "cd M3 k E" using cdS by simp
      then have "cd M' k E" by (rule cd_back_sig_steps[OF s])
      then show ?thesis using cdS by blast
    next
      assume "\<exists>M12. N1 \<rightarrow>\<^sub>n M12 \<and> M3 \<rightarrow>\<^sub>\<beta> M12"
      then obtain M12 where n1: "N1 \<rightarrow>\<^sub>n M12" and m3: "M3 \<rightarrow>\<^sub>\<beta> M12" by blast
      have "k < n" using cdS by simp
      from less.IH[OF this cdS(3) less.prems(2) n1] obtain m where "m < k" "cd M12 m E" by blast
      then have "cd M3 (Suc m) E" using cd_back_beta[OF m3] by blast
      then have "cd M' (Suc m) E" by (rule cd_back_sig_steps[OF s])
      then show ?thesis using cdS \<open>m < k\<close> by auto
    qed
  qed
qed

lemma cd_SNn: "cd M n E \<Longrightarrow> fb E \<Longrightarrow> SN_at cbvn M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. cd M n E \<Longrightarrow> SN_at cbvn M"
  proof -
    fix M
    show "cd M n E \<Longrightarrow> SN_at cbvn M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "cbvn M N"
        then consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>n N" by (auto simp: cbvn_def)
        then show "SN_at cbvn N"
        proof cases
          case 1
          have "cd N n E" using cd_fwd_sig[OF 1 less.prems] .
          moreover have "tlength N < tlength M" using sig_tlength_decrease[OF 1] .
          ultimately show ?thesis using less.hyps by blast
        next
          case 2
          then obtain m where "m < n" "cd N m E" using cd_betan less.prems \<open>fb E\<close> by blast
          then show ?thesis using IHn \<open>fb E\<close> by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma cd_reach_n: "cbvn\<^sup>*\<^sup>* M N \<Longrightarrow> cd M n E \<Longrightarrow> fb E \<Longrightarrow> \<exists>m. cd N m E"
proof (induction arbitrary: n rule: rtranclp_induct)
  case base then show ?case by blast
next
  case (step N P)
  then obtain m where c: "cd N m E" by blast
  from step.hyps(2) consider "N \<rightarrow>\<^sub>\<sigma> P" | "N \<rightarrow>\<^sub>n P" by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_fwd_sig c by blast
  next
    case 2 then show ?thesis using cd_betan[OF c step.prems(2)] by blast
  qed
qed

theorem CFN_imp_CFSNn: "CFN M \<Longrightarrow> CFSNn M"
proof -
  assume "CFN M"
  then obtain E where r: "M \<rightarrow>\<^sub>v\<^sup>* E" and n: "NF E" and f: "fb E" by (auto simp: CFN_def)
  from steps_cd[OF r n] obtain k where c: "cd M k E" by blast
  have "SN_at cbvn M" by (rule cd_SNn[OF c f])
  moreover have "fb N" if "cbvn\<^sup>*\<^sup>* M N" "normal cbvn N" for N
  proof -
    from cd_reach_n[OF that(1) c f] obtain m where "cd N m E" by blast
    moreover have "cd N 0 N" using NF_cd normal_cbvn_NF[OF that(2)] by blast
    ultimately have "N = E" using cd_det by blast
    then show ?thesis using f by simp
  qed
  ultimately show "CFSNn M" by (auto simp: CFSNn_def)
qed

subsection \<open>Blocked terms\<close>

text \<open>Terms that can never become fireballs, whatever the order of evaluation.\<close>

inductive blk :: "trm \<Rightarrow> bool" where
  BId: "blk (App Id N)"
| BExtn: "blk (App (Extn P y Q) N)"
| BL: "blk L \<Longrightarrow> blk (App L N)"
| BR: "fb L \<Longrightarrow> blk N \<Longrightarrow> blk (App L N)"
| BLam: "blk (Comp (Var x) (Lam y B))"
| BClo: "blk (Comp (Var x) (Comp (Lam y B) K))"
| BComp: "blk M \<Longrightarrow> blk (Comp (Var x) M)"

lemma fb_Comp_Var_iff: "fb (Comp (Var x) M) \<longleftrightarrow> inert M"
proof
  assume "fb (Comp (Var x) M)"
  then have "inert (Comp (Var x) M)" by (cases rule: fb.cases) simp_all
  then show "inert M" by (cases rule: inert.cases) simp_all
next
  assume "inert M"
  then show "fb (Comp (Var x) M)" by (blast intro: IComp FInert)
qed

lemma blk_not_fb: "blk M \<Longrightarrow> \<not> fb M"
proof (induction rule: blk.induct)
  case (BL L N) then show ?case using FInert by (auto simp: fb_App_iff)
next
  case (BComp M x) then show ?case using FInert by (auto simp: fb_Comp_Var_iff)
qed (simp_all add: fb_App_iff fb_Comp_Var_iff)

lemma blk_shape: "blk M \<Longrightarrow> (\<exists>L N. M = App L N) \<or> (\<exists>x K. M = Comp (Var x) K)"
  by (induction rule: blk.induct) auto

lemma blk_step: "blk M \<Longrightarrow> cbvn M M' \<Longrightarrow> blk M'"
proof (induction arbitrary: M' rule: blk.induct)
  case (BId N)
  from BId.prems consider (s) "App Id N \<rightarrow>\<^sub>\<sigma> M'" | (b) "App Id N \<rightarrow>\<^sub>n M'" by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (AppL L') then show ?thesis by (auto elim: sig.cases)
    next
      case (AppR N') then show ?thesis by (simp add: blk.BId)
    qed
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (AppL L') then show ?thesis by (auto elim: betan.cases)
    next
      case (AppR N') then show ?thesis by (simp add: blk.BId)
    qed
  qed
next
  case (BExtn P y Q N)
  from BExtn.prems consider (s) "App (Extn P y Q) N \<rightarrow>\<^sub>\<sigma> M'" | (b) "App (Extn P y Q) N \<rightarrow>\<^sub>n M'"
    by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (AppL L')
      from AppL(2) obtain P' Q' where "L' = Extn P' y Q'" by (cases rule: sig.cases) auto
      then show ?thesis using AppL by (simp add: blk.BExtn)
    next
      case (AppR N') then show ?thesis by (simp add: blk.BExtn)
    qed
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (AppL L') then show ?thesis by (auto elim: betan.cases)
    next
      case (AppR N') then show ?thesis by (simp add: blk.BExtn)
    qed
  qed
next
  case (BL L N)
  have nl: "\<not> (\<exists>x B. L = Lam x B)" "\<not> (\<exists>x B K. L = Comp (Lam x B) K)"
    using blk_shape[OF BL.hyps] by auto
  from BL.prems consider (s) "App L N \<rightarrow>\<^sub>\<sigma> M'" | (b) "App L N \<rightarrow>\<^sub>n M'" by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (AppL L') then show ?thesis using BL.IH[of L'] by (auto simp: cbvn_def intro: blk.BL)
    next
      case (AppR N') then show ?thesis using BL.hyps by (auto intro: blk.BL)
    qed
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (AppL L') then show ?thesis using BL.IH[of L'] by (auto simp: cbvn_def intro: blk.BL)
    next
      case (AppR N') then show ?thesis using BL.hyps by (auto intro: blk.BL)
    qed (use nl in auto)
  qed
next
  case (BR L N)
  from BR.prems consider (s) "App L N \<rightarrow>\<^sub>\<sigma> M'" | (b) "App L N \<rightarrow>\<^sub>n M'" by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (AppL L') then show ?thesis using BR sig_fb by (auto intro: blk.BR)
    next
      case (AppR N') then show ?thesis using BR.IH[of N'] BR.hyps by (auto simp: cbvn_def intro: blk.BR)
    qed
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (Beta1 x B K) then show ?thesis using BR.hyps blk_not_fb by blast
    next
      case (Beta2 x B) then show ?thesis using BR.hyps blk_not_fb by blast
    next
      case (AppL L') then show ?thesis using BR.hyps fb_no_betan by blast
    next
      case (AppR N') then show ?thesis using BR.IH[of N'] BR.hyps by (auto simp: cbvn_def intro: blk.BR)
    qed
  qed
next
  case (BLam x y B)
  from BLam.prems consider (s) "Comp (Var x) (Lam y B) \<rightarrow>\<^sub>\<sigma> M'" | (b) "Comp (Var x) (Lam y B) \<rightarrow>\<^sub>n M'"
    by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (CompL P) then show ?thesis by (auto elim: sig.cases)
    next
      case (CompR P)
      from CompR(2) obtain B' where "P = Lam y B'" by (cases rule: sig.cases) auto
      then show ?thesis using CompR by (simp add: blk.BLam)
    qed
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (VarR P) then show ?thesis by (auto elim: betan.cases)
    qed
  qed
next
  case (BClo x y B K)
  from BClo.prems consider (s) "Comp (Var x) (Comp (Lam y B) K) \<rightarrow>\<^sub>\<sigma> M'"
    | (b) "Comp (Var x) (Comp (Lam y B) K) \<rightarrow>\<^sub>n M'" by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (CompR K')
      note outer = CompR
      from outer(2) show ?thesis
      proof (cases rule: sig.cases)
        case IdR then show ?thesis using outer by (auto intro: blk.BLam)
      next
        case (CompL P)
        from CompL(2) obtain B' where "P = Lam y B'" by (cases rule: sig.cases) auto
        then show ?thesis using outer CompL by (simp add: blk.BClo)
      next
        case (CompR P) then show ?thesis using outer by (auto intro: blk.BClo)
      qed
    qed (auto elim: sig.cases)
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (VarR P) then show ?thesis by (auto elim: betan.cases)
    qed
  qed
next
  case (BComp M x)
  have nm: "M \<noteq> Id" "\<forall>P y Q. M \<noteq> Extn P y Q" using blk_shape[OF BComp.hyps] by auto
  from BComp.prems consider (s) "Comp (Var x) M \<rightarrow>\<^sub>\<sigma> M'" | (b) "Comp (Var x) M \<rightarrow>\<^sub>n M'"
    by (auto simp: cbvn_def)
  then show ?case
  proof cases
    case s
    then show ?thesis
    proof (cases rule: sig.cases)
      case (CompR K') then show ?thesis using BComp.IH[of K'] by (auto simp: cbvn_def intro: blk.BComp)
    qed (use nm in \<open>auto elim: sig.cases\<close>)
  next
    case b
    then show ?thesis
    proof (cases rule: betan.cases)
      case (VarR K') then show ?thesis using BComp.IH[of K'] by (auto simp: cbvn_def intro: blk.BComp)
    qed
  qed
qed

lemma blk_steps: "cbvn\<^sup>*\<^sup>* M N \<Longrightarrow> blk M \<Longrightarrow> blk N"
  by (induction rule: rtranclp_induct) (auto intro: blk_step)

lemma NF_not_fb_blk: "NF M \<Longrightarrow> \<not> fb M \<Longrightarrow> blk M"
proof (induction M)
  case (Var x) then show ?case by simp
next
  case (Lam x M) then show ?case by (simp add: FLam)
next
  case Id then show ?case by (simp add: FId)
next
  case (Extn M1 x M2) then show ?case by (simp add: FExtn)
next
  case (App L N)
  have nL: "NF L" using App.prems(1) by (auto simp: normal_def dest: cbv_AppL)
  show ?case
  proof (cases "fb L")
    case False then show ?thesis using App.IH(1) nL by (blast intro: BL)
  next
    case True
    have nN: "NF N" using App.prems(1) True by (auto simp: normal_def cbv_def intro: sig.AppR beta.AppR)
    show ?thesis
    proof (cases "fb N")
      case False then show ?thesis using App.IH(2) nN True by (blast intro: BR)
    next
      case fN: True
      from True show ?thesis
      proof (cases rule: fb_cases)
        case inert then show ?thesis using fN App.prems(2) by (simp add: fb_App_iff)
      next
        case (lam x B)
        then have "App L N \<rightarrow>\<^sub>v Comp B (Extn N x Id)" using fN by (simp add: beta_imp_cbv beta.Beta2)
        then show ?thesis using App.prems(1) by (auto simp: normal_def)
      next
        case (clo x B K)
        then have "App L N \<rightarrow>\<^sub>v Comp B (Extn N x K)" using fN by (simp add: beta_imp_cbv beta.Beta1)
        then show ?thesis using App.prems(1) by (auto simp: normal_def)
      next
        case id then show ?thesis by (simp add: BId)
      next
        case (extn P y Q) then show ?thesis by (simp add: BExtn)
      qed
    qed
  qed
next
  case (Comp M1 M2)
  have r: "\<not> Comp M1 M2 \<rightarrow>\<^sub>\<sigma> P" for P using Comp.prems(1) by (auto simp: normal_def cbv_def)
  show ?case
  proof (cases M1)
    case (Var x)
    have n2: "NF M2" using Comp.prems(1) Var by (auto simp: normal_def dest: cbv_VarR)
    show ?thesis
    proof (cases "fb M2")
      case False then show ?thesis using Comp.IH(2) n2 Var by (blast intro: BComp)
    next
      case True
      then show ?thesis
      proof (cases rule: fb_cases)
        case inert then show ?thesis using Comp.prems(2) Var by (simp add: FInert IComp)
      next
        case (lam y B) then show ?thesis using Var by (simp add: BLam)
      next
        case (clo y B K) then show ?thesis using Var by (simp add: BClo)
      next
        case id then show ?thesis using r Var sig.IdR by blast
      next
        case (extn P y Q)
        then show ?thesis using r Var sig.VarRef sig.VarSkip by (cases "y = x") blast+
      qed
    qed
  next
    case (Lam x B) then show ?thesis using Comp.prems(2) by (simp add: FClo)
  next
    case (App P Q) then show ?thesis using r sig.DApp by blast
  next
    case Id then show ?thesis using r sig.IdL by blast
  next
    case (Extn P y Q) then show ?thesis using r sig.DExtn by blast
  next
    case (Comp P Q) then show ?thesis using r sig.Ass by blast
  qed
qed

lemma SN_at_mono: "SN_at R M \<Longrightarrow> (\<And>a b. S a b \<Longrightarrow> R a b) \<Longrightarrow> SN_at S M"
proof (induction rule: SN_at_induct)
  case (step a) then show ?case by (blast intro: SN_atI)
qed

lemma SN_normal_reach: "SN_at R a \<Longrightarrow> \<exists>b. R\<^sup>*\<^sup>* a b \<and> normal R b"
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof (cases "normal R a")
    case True then show ?thesis by blast
  next
    case False
    then obtain b where "R a b" by (auto simp: normal_def)
    with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

lemma cbv_steps_cbvn: "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> cbvn\<^sup>*\<^sup>* M N"
  by (rule steps_lift[of cbv cbvn "\<lambda>P. P"]) (rule cbv_imp_cbvn)

theorem CFSNn_imp_CFN: "CFSNn M \<Longrightarrow> CFN M"
proof -
  assume c: "CFSNn M"
  then have sn: "SN_at cbvn M" and cf: "\<And>N. cbvn\<^sup>*\<^sup>* M N \<Longrightarrow> normal cbvn N \<Longrightarrow> fb N"
    by (auto simp: CFSNn_def)
  have "SN_at cbv M" by (rule SN_at_mono[OF sn cbv_imp_cbvn])
  from SN_normal_reach[OF this] obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" by blast
  have rn: "cbvn\<^sup>*\<^sup>* M N" by (rule cbv_steps_cbvn[OF r])
  have "fb N"
  proof (rule ccontr)
    assume "\<not> fb N"
    then have b: "blk N" using NF_not_fb_blk n by blast
    have "SN_at cbvn N" using SN_at_rtranclp[OF sn rn] .
    from SN_normal_reach[OF this] obtain P where rp: "cbvn\<^sup>*\<^sup>* N P" and np: "normal cbvn P" by blast
    have "blk P" by (rule blk_steps[OF rp b])
    moreover have "fb P" using cf[OF rtranclp_trans[OF rn rp] np] .
    ultimately show False using blk_not_fb by blast
  qed
  then show "CFN M" using r n by (auto simp: CFN_def)
qed

theorem main_characterization_any_order: "Typ M \<longleftrightarrow> CFSNn M"
  using main_characterization CFN_imp_CFSNn CFSNn_imp_CFN by blast

end
