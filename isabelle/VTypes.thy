theory VTypes
  imports Lambda
begin

section \<open>A classical call-by-value intersection-type system on de Bruijn terms\<close>

text \<open>
  Types are built from type variables, a constant \<open>\<nu>\<close>, arrows and
  intersections, ordered by the usual subtyping (without arrow distributivity),
  with every type below \<open>\<nu>\<close>.  As in the call-by-value systems of
  Ronchi Della Rocca and Paolini, \<open>\<nu>\<close> is given to abstractions by an axiom
  (and to variables through the context); there is no rule giving a type to an
  arbitrary term.  It is an idempotent counterpart of Ehrhard's call-by-value
  multi types, used by Accattoli and Guerrieri for Open CBV.
  Main result \<open>classical_VN\<close>: a term is normalizable in Open CBV (the fireball
  calculus) iff it is typable.
\<close>

datatype vty = VTV nat | VNu | VArr vty vty | VInter vty vty

inductive vsub :: "vty \<Rightarrow> vty \<Rightarrow> bool" (infix "\<le>\<^sub>v" 50) where
  vs_refl: "A \<le>\<^sub>v A"
| vs_trans: "A \<le>\<^sub>v B \<Longrightarrow> B \<le>\<^sub>v C \<Longrightarrow> A \<le>\<^sub>v C"
| vs_nu: "A \<le>\<^sub>v VNu"
| vs_inter1: "VInter A B \<le>\<^sub>v A"
| vs_inter2: "VInter A B \<le>\<^sub>v B"
| vs_glb: "A \<le>\<^sub>v B \<Longrightarrow> A \<le>\<^sub>v C \<Longrightarrow> A \<le>\<^sub>v VInter B C"
| vs_arr: "A' \<le>\<^sub>v A \<Longrightarrow> B \<le>\<^sub>v B' \<Longrightarrow> VArr A B \<le>\<^sub>v VArr A' B'"

definition scons :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" (infixr "##" 65) where
  "scons a f = (\<lambda>i. case i of 0 \<Rightarrow> a | Suc j \<Rightarrow> f j)"

lemma scons_0 [simp]: "(a ## f) 0 = a"
  by (simp add: scons_def)

lemma scons_Suc [simp]: "(a ## f) (Suc j) = f j"
  by (simp add: scons_def)

lemma scons_comp_Suc [simp]: "(a ## f) \<circ> Suc = f"
  by (rule ext) simp

lemma scons_eta: "(f 0 ## (\<lambda>i. f (Suc i))) = f"
proof (rule ext)
  fix i show "(f 0 ## (\<lambda>i. f (Suc i))) i = f i" by (cases i) simp_all
qed

inductive vty_of :: "(nat \<Rightarrow> vty) \<Rightarrow> dB \<Rightarrow> vty \<Rightarrow> bool" ("_ \<turnstile>\<^sub>v _ : _" [50, 0, 50] 50) where
  vVar: "\<Gamma> i = A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v DVar i : A"
| vAbs: "(A ## \<Gamma>) \<turnstile>\<^sub>v t : B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v DAbs t : VArr A B"
| vApp: "\<Gamma> \<turnstile>\<^sub>v s : VArr A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v u : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v DApp s u : B"
| vNu: "\<Gamma> \<turnstile>\<^sub>v DAbs t : VNu"
| vInter: "\<Gamma> \<turnstile>\<^sub>v t : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v t : B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v t : VInter A B"
| vSub: "\<Gamma> \<turnstile>\<^sub>v t : A \<Longrightarrow> A \<le>\<^sub>v B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v t : B"

subsection \<open>Renamings and simultaneous substitution\<close>

definition rup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "rup r = (\<lambda>i. case i of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> Suc (r j))"

lemma rup_0 [simp]: "rup r 0 = 0"
  by (simp add: rup_def)

lemma rup_Suc [simp]: "rup r (Suc j) = Suc (r j)"
  by (simp add: rup_def)

primrec dbren :: "dB \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> dB" where
  "dbren (DVar i) r = DVar (r i)"
| "dbren (DApp s t) r = DApp (dbren s r) (dbren t r)"
| "dbren (DAbs s) r = DAbs (dbren s (rup r))"

definition dbup :: "(nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" where
  "dbup s = (\<lambda>i. case i of 0 \<Rightarrow> DVar 0 | Suc j \<Rightarrow> dbren (s j) Suc)"

lemma dbup_0 [simp]: "dbup s 0 = DVar 0"
  by (simp add: dbup_def)

lemma dbup_Suc [simp]: "dbup s (Suc j) = dbren (s j) Suc"
  by (simp add: dbup_def)

primrec dbsub :: "dB \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> dB" where
  "dbsub (DVar i) s = s i"
| "dbsub (DApp t u) s = DApp (dbsub t s) (dbsub u s)"
| "dbsub (DAbs t) s = DAbs (dbsub t (dbup s))"

lemma rup_comp: "rup r' \<circ> rup r = rup (r' \<circ> r)"
proof (rule ext)
  fix i show "(rup r' \<circ> rup r) i = rup (r' \<circ> r) i" by (cases i) simp_all
qed

lemma ren_ren: "dbren (dbren t r) r' = dbren t (r' \<circ> r)"
  by (induct t arbitrary: r r') (simp_all add: rup_comp)

lemma dbup_rup: "dbup s \<circ> rup r = dbup (s \<circ> r)"
proof (rule ext)
  fix i show "(dbup s \<circ> rup r) i = dbup (s \<circ> r) i" by (cases i) simp_all
qed

lemma sub_ren: "dbsub (dbren t r) s = dbsub t (s \<circ> r)"
  by (induct t arbitrary: r s) (simp_all add: dbup_rup)

lemma ren_dbup: "(\<lambda>i. dbren (dbup s i) (rup r)) = dbup (\<lambda>i. dbren (s i) r)"
proof (rule ext)
  fix i show "dbren (dbup s i) (rup r) = dbup (\<lambda>i. dbren (s i) r) i"
    by (cases i) (simp_all add: ren_ren comp_def)
qed

lemma ren_sub: "dbren (dbsub t s) r = dbsub t (\<lambda>i. dbren (s i) r)"
  by (induct t arbitrary: r s) (simp_all add: ren_dbup)

lemma sub_dbup: "(\<lambda>i. dbsub (dbup s i) (dbup \<tau>)) = dbup (\<lambda>i. dbsub (s i) \<tau>)"
proof (rule ext)
  fix i show "dbsub (dbup s i) (dbup \<tau>) = dbup (\<lambda>i. dbsub (s i) \<tau>) i"
  proof (cases i)
    case 0 then show ?thesis by simp
  next
    case (Suc j)
    have "dbsub (dbren (s j) Suc) (dbup \<tau>) = dbsub (s j) (dbup \<tau> \<circ> Suc)"
      by (rule sub_ren)
    also have "dbup \<tau> \<circ> Suc = (\<lambda>i. dbren (\<tau> i) Suc)" by (rule ext) simp
    also have "dbsub (s j) (\<lambda>i. dbren (\<tau> i) Suc) = dbren (dbsub (s j) \<tau>) Suc"
      by (rule ren_sub[symmetric])
    finally show ?thesis using Suc by simp
  qed
qed

lemma sub_sub: "dbsub (dbsub t s) \<tau> = dbsub t (\<lambda>i. dbsub (s i) \<tau>)"
  by (induct t arbitrary: s \<tau>) (simp_all add: sub_dbup)

lemma dbup_var: "dbup DVar = DVar"
proof (rule ext)
  fix i show "dbup DVar i = DVar i" by (cases i) simp_all
qed

lemma sub_var [simp]: "dbsub t DVar = t"
  by (induct t) (simp_all add: dbup_var)

definition dl :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dl k = (\<lambda>i. if i < k then i else Suc i)"

lemma dl_simp [simp]: "dl k i = (if i < k then i else Suc i)"
  by (simp add: dl_def)

lemma rup_dl: "rup (dl k) = dl (Suc k)"
proof (rule ext)
  fix i show "rup (dl k) i = dl (Suc k) i" by (cases i) simp_all
qed

lemma lift_ren: "lift t k = dbren t (dl k)"
  by (induct t arbitrary: k) (simp_all add: rup_dl)

lemma dl_0: "dl 0 = Suc"
  by (rule ext) simp

definition ins :: "nat \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB" where
  "ins k u i = (if i < k then DVar i else if i = k then u else DVar (i - 1))"

lemma dbup_ins: "dbup (ins k u) = ins (Suc k) (lift u 0)"
proof (rule ext)
  fix i show "dbup (ins k u) i = ins (Suc k) (lift u 0) i"
  proof (cases i)
    case 0 then show ?thesis by (simp add: ins_def)
  next
    case (Suc j)
    show ?thesis
    proof (cases "j < k")
      case True with Suc show ?thesis by (simp add: ins_def)
    next
      case False
      show ?thesis
      proof (cases "j = k")
        case True with Suc show ?thesis by (simp add: ins_def lift_ren dl_0)
      next
        case False with \<open>\<not> j < k\<close> Suc show ?thesis
          by (cases j) (simp_all add: ins_def)
      qed
    qed
  qed
qed

lemma subst_sub: "t[u/k] = dbsub t (ins k u)"
  by (induct t arbitrary: k u) (simp_all add: subst_Var dbup_ins ins_def)

lemma lift_subst0: "lift (s[t/0]) k = (lift s (Suc k))[lift t k/0]"
proof -
  have "lift (s[t/0]) k = dbren (dbsub s (ins 0 t)) (dl k)"
    by (simp add: subst_sub lift_ren)
  also have "\<dots> = dbsub s (\<lambda>i. dbren (ins 0 t i) (dl k))" by (rule ren_sub)
  also have "(\<lambda>i. dbren (ins 0 t i) (dl k)) = ins 0 (lift t k) \<circ> dl (Suc k)"
  proof (rule ext)
    fix i show "dbren (ins 0 t i) (dl k) = (ins 0 (lift t k) \<circ> dl (Suc k)) i"
      by (cases i) (simp_all add: ins_def lift_ren)
  qed
  also have "dbsub s (ins 0 (lift t k) \<circ> dl (Suc k)) = dbsub (dbren s (dl (Suc k))) (ins 0 (lift t k))"
    by (rule sub_ren[symmetric])
  also have "\<dots> = (lift s (Suc k))[lift t k/0]" by (simp add: subst_sub lift_ren)
  finally show ?thesis .
qed

lemma sub_up: "(dbsub t (dbup \<sigma>))[u/0] = dbsub t (u ## \<sigma>)"
proof -
  have "(dbsub t (dbup \<sigma>))[u/0] = dbsub (dbsub t (dbup \<sigma>)) (ins 0 u)"
    by (rule subst_sub)
  also have "\<dots> = dbsub t (\<lambda>i. dbsub (dbup \<sigma> i) (ins 0 u))" by (rule sub_sub)
  also have "(\<lambda>i. dbsub (dbup \<sigma> i) (ins 0 u)) = (u ## \<sigma>)"
  proof (rule ext)
    fix i show "dbsub (dbup \<sigma> i) (ins 0 u) = (u ## \<sigma>) i"
    proof (cases i)
      case 0 then show ?thesis by (simp add: ins_def)
    next
      case (Suc j)
      have "ins 0 u \<circ> Suc = DVar" by (rule ext) (simp add: ins_def)
      then show ?thesis using Suc by (simp add: sub_ren)
    qed
  qed
  finally show ?thesis .
qed


subsection \<open>Facts about Open CBV\<close>

lemma vappL_star: "vred\<^sup>*\<^sup>* s s' \<Longrightarrow> vred\<^sup>*\<^sup>* (DApp s t) (DApp s' t)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl vred.vappL)

lemma vappR_star:
  assumes "dfb s" "vred\<^sup>*\<^sup>* t t'"
  shows "vred\<^sup>*\<^sup>* (DApp s t) (DApp s t')"
  using assms(2) by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl vred.vappR assms(1))

lemma normal_dfb: "normal vred u \<Longrightarrow> dfb u"
proof (induction u)
  case (DVar i) then show ?case by (auto intro: dinert_dfb.intros)
next
  case (DAbs s) then show ?case by (auto intro: dinert_dfb.intros)
next
  case (DApp s t)
  have ns: "normal vred s"
    using DApp.prems by (auto simp: normal_def intro: vred.vappL)
  then have fs: "dfb s" using DApp.IH(1) by blast
  have nt: "normal vred t"
    using DApp.prems fs by (auto simp: normal_def intro: vred.vappR)
  then have ft: "dfb t" using DApp.IH(2) by blast
  show ?case
  proof (cases "\<exists>s0. s = DAbs s0")
    case True
    then obtain s0 where "s = DAbs s0" by blast
    with ft DApp.prems show ?thesis by (auto simp: normal_def intro: vred.vbeta)
  next
    case False
    with fs have "dinert s" by (auto elim: dfb.cases)
    with ft show ?thesis by (auto intro: dinert_dfb.intros)
  qed
qed

lemma vred_star_normal_unique:
  assumes "vred\<^sup>*\<^sup>* t u" "vred\<^sup>*\<^sup>* t u'" "normal vred u" "normal vred u'"
  shows "u = u'"
  using assms(1,2,4)
proof (induction arbitrary: u' rule: converse_rtranclp_induct)
  case base
  then show ?case using assms(3) by (auto simp: normal_def elim: converse_rtranclpE)
next
  case (step y z)
  from step.prems(1) show ?case
  proof (rule converse_rtranclpE)
    assume "y = u'"
    then have "\<not> normal vred y" using step.hyps(1) by (auto simp: normal_def)
    then show ?thesis using \<open>y = u'\<close> step.prems(2) by simp
  next
    fix z' assume a: "y \<rightarrow>\<^sub>f z'" "vred\<^sup>*\<^sup>* z' u'"
    then have "z' = z" using step.hyps(1) vred_det by blast
    then show ?thesis using step.IH a(2) step.prems(2) by blast
  qed
qed

subsection \<open>Soundness: a realizability interpretation\<close>

text \<open>
  A type denotes a set of fireballs; a term realizes a type when it evaluates to
  a fireball in that set.  Inert terms belong to every type.
\<close>

definition evals :: "dB set \<Rightarrow> dB set" where
  "evals S = {t. \<exists>f. vred\<^sup>*\<^sup>* t f \<and> f \<in> S}"

fun vsem :: "vty \<Rightarrow> dB set" where
  "vsem (VTV a) = {f. dfb f}"
| "vsem VNu = {f. dfb f}"
| "vsem (VArr A B) = {f. dfb f \<and> (\<forall>g \<in> vsem A. DApp f g \<in> evals (vsem B))}"
| "vsem (VInter A B) = vsem A \<inter> vsem B"

lemma vsem_dfb: "f \<in> vsem A \<Longrightarrow> dfb f"
  by (induction A) auto

lemma vsem_inert: "dinert i \<Longrightarrow> i \<in> vsem A"
proof (induction A arbitrary: i)
  case (VArr A B)
  have "DApp i g \<in> evals (vsem B)" if "g \<in> vsem A" for g
  proof -
    have "dinert (DApp i g)" using VArr.prems vsem_dfb[OF that] by (auto intro: dinert_dfb.intros)
    then have "DApp i g \<in> vsem B" using VArr.IH(2) by blast
    then show ?thesis by (auto simp: evals_def)
  qed
  then show ?case using VArr.prems by (auto intro: dinert_dfb.intros)
qed (auto intro: dinert_dfb.intros)

lemma vsem_sub: "A \<le>\<^sub>v B \<Longrightarrow> vsem A \<subseteq> vsem B"
proof (induction rule: vsub.induct)
  case (vs_nu A) then show ?case using vsem_dfb by auto
next
  case (vs_arr A' A B B')
  show ?case
  proof
    fix f assume f: "f \<in> vsem (VArr A B)"
    have "DApp f g \<in> evals (vsem B')" if g: "g \<in> vsem A'" for g
    proof -
      from g vs_arr.IH(1) have "g \<in> vsem A" by blast
      with f obtain h where "vred\<^sup>*\<^sup>* (DApp f g) h" "h \<in> vsem B" by (auto simp: evals_def)
      with vs_arr.IH(2) show ?thesis by (auto simp: evals_def)
    qed
    then show "f \<in> vsem (VArr A' B')" using f by simp
  qed
qed auto

lemma evals_inter:
  assumes "t \<in> evals (vsem A)" "t \<in> evals (vsem B)"
  shows "t \<in> evals (vsem (VInter A B))"
proof -
  from assms obtain f g where f: "vred\<^sup>*\<^sup>* t f" "f \<in> vsem A" and g: "vred\<^sup>*\<^sup>* t g" "g \<in> vsem B"
    by (auto simp: evals_def)
  have "normal vred f" "normal vred g" using f(2) g(2) vsem_dfb dfb_normal by blast+
  then have "f = g" using f(1) g(1) vred_star_normal_unique by blast
  then show ?thesis using f g by (auto simp: evals_def)
qed

lemma fund:
  assumes "\<Gamma> \<turnstile>\<^sub>v t : A"
  shows "(\<forall>i. \<sigma> i \<in> vsem (\<Gamma> i)) \<Longrightarrow> dbsub t \<sigma> \<in> evals (vsem A)"
using assms
proof (induction arbitrary: \<sigma> rule: vty_of.induct)
  case (vVar \<Gamma> i A)
  then show ?case by (auto simp: evals_def)
next
  case (vAbs A \<Gamma> t B)
  let ?F = "DAbs (dbsub t (dbup \<sigma>))"
  have "DApp ?F g \<in> evals (vsem B)" if g: "g \<in> vsem A" for g
  proof -
    have "\<forall>i. (g ## \<sigma>) i \<in> vsem ((A ## \<Gamma>) i)"
    proof
      fix i show "(g ## \<sigma>) i \<in> vsem ((A ## \<Gamma>) i)" using g vAbs.prems by (cases i) simp_all
    qed
    then have h: "dbsub t (g ## \<sigma>) \<in> evals (vsem B)" using vAbs.IH by blast
    have "DApp ?F g \<rightarrow>\<^sub>f (dbsub t (dbup \<sigma>))[g/0]"
      using vsem_dfb[OF g] by (rule vred.vbeta)
    then have "DApp ?F g \<rightarrow>\<^sub>f dbsub t (g ## \<sigma>)" by (simp add: sub_up)
    with h show ?thesis by (auto simp: evals_def intro: converse_rtranclp_into_rtranclp)
  qed
  then have "?F \<in> vsem (VArr A B)" by (auto intro: dinert_dfb.intros)
  then show ?case by (auto simp: evals_def)
next
  case (vApp \<Gamma> s A B u)
  from vApp.IH(1)[OF vApp.prems] obtain f where
    f: "vred\<^sup>*\<^sup>* (dbsub s \<sigma>) f" "f \<in> vsem (VArr A B)" by (auto simp: evals_def)
  from vApp.IH(2)[OF vApp.prems] obtain g where
    g: "vred\<^sup>*\<^sup>* (dbsub u \<sigma>) g" "g \<in> vsem A" by (auto simp: evals_def)
  from f(2) g(2) obtain h where h: "vred\<^sup>*\<^sup>* (DApp f g) h" "h \<in> vsem B"
    by (auto simp: evals_def)
  have "vred\<^sup>*\<^sup>* (DApp (dbsub s \<sigma>) (dbsub u \<sigma>)) (DApp f (dbsub u \<sigma>))"
    using f(1) by (rule vappL_star)
  also have "vred\<^sup>*\<^sup>* \<dots> (DApp f g)"
    using vsem_dfb[OF f(2)] g(1) by (rule vappR_star)
  also have "vred\<^sup>*\<^sup>* \<dots> h" by (rule h(1))
  finally show ?case using h(2) by (auto simp: evals_def)
next
  case (vNu \<Gamma> t)
  then show ?case by (auto simp: evals_def intro: dinert_dfb.intros)
next
  case (vInter \<Gamma> t A B)
  then show ?case using evals_inter by blast
next
  case (vSub \<Gamma> t A B)
  then show ?case using vsem_sub by (fastforce simp: evals_def)
qed

theorem classical_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>v t : A"
  shows "lam_VN t"
proof -
  have "\<forall>i. DVar i \<in> vsem (\<Gamma> i)" by (auto intro: vsem_inert dinert_dfb.intros)
  from fund[OF assms this] obtain f where "vred\<^sup>*\<^sup>* t f" "f \<in> vsem A"
    by (auto simp: evals_def)
  then show ?thesis using vsem_dfb dfb_normal by (auto simp: lam_VN_def)
qed

subsection \<open>Completeness: typing lemmas and subject expansion\<close>

definition cle :: "(nat \<Rightarrow> vty) \<Rightarrow> (nat \<Rightarrow> vty) \<Rightarrow> bool" where
  "cle \<Gamma>' \<Gamma> \<longleftrightarrow> (\<forall>i. \<Gamma>' i \<le>\<^sub>v \<Gamma> i)"

definition cmeet :: "(nat \<Rightarrow> vty) \<Rightarrow> (nat \<Rightarrow> vty) \<Rightarrow> nat \<Rightarrow> vty" where
  "cmeet \<Gamma>1 \<Gamma>2 = (\<lambda>i. VInter (\<Gamma>1 i) (\<Gamma>2 i))"

lemma cle_refl: "cle \<Gamma> \<Gamma>"
  by (simp add: cle_def vs_refl)

lemma cle_trans: "cle \<Gamma>1 \<Gamma>2 \<Longrightarrow> cle \<Gamma>2 \<Gamma>3 \<Longrightarrow> cle \<Gamma>1 \<Gamma>3"
  by (auto simp: cle_def intro: vs_trans)

lemma cle_meet1: "cle (cmeet \<Gamma>1 \<Gamma>2) \<Gamma>1"
  by (simp add: cle_def cmeet_def vs_inter1)

lemma cle_meet2: "cle (cmeet \<Gamma>1 \<Gamma>2) \<Gamma>2"
  by (simp add: cle_def cmeet_def vs_inter2)

lemma cle_glb: "cle \<Gamma> \<Gamma>1 \<Longrightarrow> cle \<Gamma> \<Gamma>2 \<Longrightarrow> cle \<Gamma> (cmeet \<Gamma>1 \<Gamma>2)"
  by (simp add: cle_def cmeet_def vs_glb)

lemma gen_var_aux: "\<Gamma> \<turnstile>\<^sub>v r : C \<Longrightarrow> \<forall>i. r = DVar i \<longrightarrow> \<Gamma> i \<le>\<^sub>v C"
  by (induction rule: vty_of.induct) (auto intro: vsub.intros)

lemma gen_var: "\<Gamma> \<turnstile>\<^sub>v DVar i : C \<Longrightarrow> \<Gamma> i \<le>\<^sub>v C"
  using gen_var_aux by blast

lemma ctx_mono_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>v t : A"
  shows "\<forall>\<Gamma>'. (\<forall>i. \<Gamma>' i \<le>\<^sub>v \<Gamma> i) \<longrightarrow> \<Gamma>' \<turnstile>\<^sub>v t : A"
using assms
proof (induction rule: vty_of.induct)
  case (vVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix \<Gamma>' assume h: "\<forall>i. \<Gamma>' i \<le>\<^sub>v \<Gamma> i"
    have "\<Gamma>' \<turnstile>\<^sub>v DVar i : \<Gamma>' i" by (rule vty_of.vVar) simp
    moreover from h vVar.hyps have "\<Gamma>' i \<le>\<^sub>v A" by blast
    ultimately show "\<Gamma>' \<turnstile>\<^sub>v DVar i : A" by (rule vty_of.vSub)
  qed
next
  case (vAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<Gamma>' assume h: "\<forall>i. \<Gamma>' i \<le>\<^sub>v \<Gamma> i"
    have "\<forall>i. (A ## \<Gamma>') i \<le>\<^sub>v (A ## \<Gamma>) i"
    proof
      fix i show "(A ## \<Gamma>') i \<le>\<^sub>v (A ## \<Gamma>) i" using h by (cases i) (simp_all add: vs_refl)
    qed
    with vAbs.IH have "(A ## \<Gamma>') \<turnstile>\<^sub>v t : B" by blast
    then show "\<Gamma>' \<turnstile>\<^sub>v DAbs t : VArr A B" by (rule vty_of.vAbs)
  qed
qed (blast intro: vty_of.intros)+

lemma ctx_mono: "\<Gamma> \<turnstile>\<^sub>v t : A \<Longrightarrow> cle \<Gamma>' \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>v t : A"
  using ctx_mono_aux by (auto simp: cle_def)

lemma weaken_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>v t : A"
  shows "\<forall>\<rho> (\<Gamma>' :: nat \<Rightarrow> vty). (\<forall>i. \<Gamma>' (\<rho> i) = \<Gamma> i) \<longrightarrow> \<Gamma>' \<turnstile>\<^sub>v dbren t \<rho> : A"
using assms
proof (induction rule: vty_of.induct)
  case (vVar \<Gamma> i A) then show ?case by (auto intro: vty_of.vVar)
next
  case (vAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<rho> and \<Gamma>' :: "nat \<Rightarrow> vty" assume h: "\<forall>i. \<Gamma>' (\<rho> i) = \<Gamma> i"
    have "\<forall>i. (A ## \<Gamma>') (rup \<rho> i) = (A ## \<Gamma>) i"
    proof
      fix i show "(A ## \<Gamma>') (rup \<rho> i) = (A ## \<Gamma>) i" using h by (cases i) simp_all
    qed
    with vAbs.IH have "(A ## \<Gamma>') \<turnstile>\<^sub>v dbren t (rup \<rho>) : B" by blast
    then show "\<Gamma>' \<turnstile>\<^sub>v dbren (DAbs t) \<rho> : VArr A B" by (simp add: vty_of.vAbs)
  qed
next
  case (vApp \<Gamma> s A B u)
  show ?case
  proof (intro allI impI)
    fix \<rho> and \<Gamma>' :: "nat \<Rightarrow> vty" assume h: "\<forall>i. \<Gamma>' (\<rho> i) = \<Gamma> i"
    have "\<Gamma>' \<turnstile>\<^sub>v dbren s \<rho> : VArr A B" using vApp.IH(1) h by blast
    moreover have "\<Gamma>' \<turnstile>\<^sub>v dbren u \<rho> : A" using vApp.IH(2) h by blast
    ultimately show "\<Gamma>' \<turnstile>\<^sub>v dbren (DApp s u) \<rho> : B" by (simp add: vty_of.vApp)
  qed
qed (auto intro: vty_of.intros)

lemma weaken: "\<Gamma> \<turnstile>\<^sub>v t : A \<Longrightarrow> (\<And>i. (\<Gamma>' :: nat \<Rightarrow> vty) (\<rho> i) = \<Gamma> i) \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>v dbren t \<rho> : A"
  using weaken_aux by blast

lemma strengthen_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>v r : A"
  shows "\<forall>\<rho> t. r = dbren t \<rho> \<longrightarrow> (\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v t : A"
using assms
proof (induction rule: vty_of.induct)
  case (vVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix \<rho> t assume e: "DVar i = dbren t \<rho>"
    then obtain j where "t = DVar j" "\<rho> j = i" by (cases t) auto
    with vVar.hyps show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v t : A" by (auto intro: vty_of.vVar)
  qed
next
  case (vAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<rho> s assume e: "DAbs t = dbren s \<rho>"
    then obtain s1 where s: "s = DAbs s1" and t: "t = dbren s1 (rup \<rho>)" by (cases s) auto
    from vAbs.IH t have "((A ## \<Gamma>) \<circ> rup \<rho>) \<turnstile>\<^sub>v s1 : B" by blast
    moreover have "(A ## \<Gamma>) \<circ> rup \<rho> = A ## (\<Gamma> \<circ> \<rho>)"
    proof (rule ext)
      fix i show "((A ## \<Gamma>) \<circ> rup \<rho>) i = (A ## (\<Gamma> \<circ> \<rho>)) i" by (cases i) simp_all
    qed
    ultimately have "(A ## (\<Gamma> \<circ> \<rho>)) \<turnstile>\<^sub>v s1 : B" by simp
    then show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v s : VArr A B" using s by (simp add: vty_of.vAbs)
  qed
next
  case (vApp \<Gamma> p A B q)
  show ?case
  proof (intro allI impI)
    fix \<rho> s assume e: "DApp p q = dbren s \<rho>"
    then obtain s1 s2 where s: "s = DApp s1 s2" and p: "p = dbren s1 \<rho>" and q: "q = dbren s2 \<rho>"
      by (cases s) auto
    from vApp.IH(1) p have "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v s1 : VArr A B" by blast
    moreover from vApp.IH(2) q have "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v s2 : A" by blast
    ultimately show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v s : B" using s by (simp add: vty_of.vApp)
  qed
next
  case (vNu \<Gamma> t)
  show ?case
  proof (intro allI impI)
    fix \<rho> s assume e: "DAbs t = dbren s \<rho>"
    then obtain s1 where "s = DAbs s1" by (cases s) auto
    then show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v s : VNu" by (simp add: vty_of.vNu)
  qed
qed (blast intro: vty_of.intros)+

lemma strengthen: "\<Gamma> \<turnstile>\<^sub>v dbren t \<rho> : A \<Longrightarrow> (\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>v t : A"
  using strengthen_aux by blast

text \<open>
  Inverting a substitution.  Every substituted term must already have type
  \<open>\<nu>\<close>: this replaces the CBN rule giving \<open>\<omega>\<close> to every term, and it is
  where call-by-value differs (only fireballs are substituted).
\<close>

lemma expand_var:
  assumes "\<Gamma> \<turnstile>\<^sub>v \<sigma> j : A" "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
  shows "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v DVar j : A"
proof -
  let ?D = "\<lambda>k. if k = j then A else VNu"
  have "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i"
  proof
    fix i show "\<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i" by (cases "i = j") (simp_all add: assms)
  qed
  moreover have "?D \<turnstile>\<^sub>v DVar j : A" by (rule vty_of.vVar) simp
  ultimately show ?thesis by (rule exI[of _ ?D, OF conjI])
qed

lemma expand_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>v r : A"
  shows "\<forall>s \<sigma>. r = dbsub s \<sigma> \<longrightarrow> (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu) \<longrightarrow>
           (\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : A)"
using assms
proof (induction rule: vty_of.induct)
  case (vVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DVar i = dbsub s \<sigma>" and nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
    then obtain j where sj: "s = DVar j" by (cases s) auto
    with e have "\<sigma> j = DVar i" by simp
    then have "\<Gamma> \<turnstile>\<^sub>v \<sigma> j : A" using vVar.hyps by (auto intro: vty_of.vVar)
    then show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : A" using sj expand_var nu by blast
  qed
next
  case (vAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DAbs t = dbsub s \<sigma>" and nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : VArr A B"
    proof (cases s)
      case (DVar j)
      with e have "\<sigma> j = DAbs t" by simp
      then have "\<Gamma> \<turnstile>\<^sub>v \<sigma> j : VArr A B" using vAbs.hyps by (auto intro: vty_of.vAbs)
      then show ?thesis using DVar expand_var nu by blast
    next
      case (DApp p q) with e show ?thesis by simp
    next
      case (DAbs s1)
      with e have e1: "t = dbsub s1 (dbup \<sigma>)" by simp
      have nu': "\<forall>i. (A ## \<Gamma>) \<turnstile>\<^sub>v dbup \<sigma> i : VNu"
      proof
        fix i show "(A ## \<Gamma>) \<turnstile>\<^sub>v dbup \<sigma> i : VNu"
        proof (cases i)
          case 0 then show ?thesis by (auto intro: vty_of.vVar vty_of.vSub vs_nu)
        next
          case (Suc j)
          have "(A ## \<Gamma>) \<turnstile>\<^sub>v dbren (\<sigma> j) Suc : VNu" using nu by (intro weaken[of \<Gamma> "\<sigma> j" VNu]) simp_all
          then show ?thesis using Suc by simp
        qed
      qed
      from vAbs.IH e1 nu' obtain \<Delta>' where
        h1: "\<forall>i. (A ## \<Gamma>) \<turnstile>\<^sub>v dbup \<sigma> i : \<Delta>' i" and h2: "\<Delta>' \<turnstile>\<^sub>v s1 : B" by blast
      let ?C = "\<Delta>' 0"
      let ?D = "\<lambda>i. \<Delta>' (Suc i)"
      have h0: "(A ## \<Gamma>) \<turnstile>\<^sub>v DVar 0 : ?C" using h1 by (metis dbup_0)
      then have "(A ## \<Gamma>) 0 \<le>\<^sub>v ?C" by (rule gen_var)
      then have AC: "A \<le>\<^sub>v ?C" by simp
      have eta: "(?C ## ?D) = \<Delta>'" by (rule scons_eta)
      from h2 eta have "(?C ## ?D) \<turnstile>\<^sub>v s1 : B" by simp
      then have "?D \<turnstile>\<^sub>v DAbs s1 : VArr ?C B" by (rule vty_of.vAbs)
      then have d: "?D \<turnstile>\<^sub>v DAbs s1 : VArr A B"
        by (rule vty_of.vSub) (rule vs_arr[OF AC vs_refl])
      have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i"
      proof
        fix i
        have "(A ## \<Gamma>) \<turnstile>\<^sub>v dbup \<sigma> (Suc i) : \<Delta>' (Suc i)" using h1 by blast
        then have "(A ## \<Gamma>) \<turnstile>\<^sub>v dbren (\<sigma> i) Suc : ?D i" by simp
        then have "((A ## \<Gamma>) \<circ> Suc) \<turnstile>\<^sub>v \<sigma> i : ?D i" by (rule strengthen)
        then show "\<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i" by simp
      qed
      show ?thesis unfolding DAbs by (rule exI[of _ ?D]) (rule conjI[OF hs d])
    qed
  qed
next
  case (vApp \<Gamma> p A B q)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DApp p q = dbsub s \<sigma>" and nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : B"
    proof (cases s)
      case (DVar j)
      with e have "\<sigma> j = DApp p q" by simp
      then have "\<Gamma> \<turnstile>\<^sub>v \<sigma> j : B" using vApp.hyps by (auto intro: vty_of.vApp)
      then show ?thesis using DVar expand_var nu by blast
    next
      case (DAbs s1) with e show ?thesis by simp
    next
      case (DApp s1 s2)
      with e have e1: "p = dbsub s1 \<sigma>" and e2: "q = dbsub s2 \<sigma>" by simp_all
      from vApp.IH(1) e1 nu obtain \<Delta>1 where
        a1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta>1 i" and a2: "\<Delta>1 \<turnstile>\<^sub>v s1 : VArr A B" by blast
      from vApp.IH(2) e2 nu obtain \<Delta>2 where
        b1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta>2 i" and b2: "\<Delta>2 \<turnstile>\<^sub>v s2 : A" by blast
      let ?D = "cmeet \<Delta>1 \<Delta>2"
      have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i" using a1 b1 by (simp add: cmeet_def vty_of.vInter)
      have d1: "?D \<turnstile>\<^sub>v s1 : VArr A B" using a2 cle_meet1 by (rule ctx_mono)
      have d2: "?D \<turnstile>\<^sub>v s2 : A" using b2 cle_meet2 by (rule ctx_mono)
      from d1 d2 have d: "?D \<turnstile>\<^sub>v DApp s1 s2 : B" by (rule vty_of.vApp)
      show ?thesis unfolding DApp by (rule exI[of _ ?D]) (rule conjI[OF hs d])
    qed
  qed
next
  case (vNu \<Gamma> t)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DAbs t = dbsub s \<sigma>" and nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : VNu"
    proof (cases s)
      case (DVar j)
      then show ?thesis using expand_var nu by blast
    next
      case (DApp p q) with e show ?thesis by simp
    next
      case (DAbs s1)
      have "(\<lambda>_. VNu) \<turnstile>\<^sub>v s : VNu" unfolding DAbs by (rule vty_of.vNu)
      then show ?thesis using nu by (intro exI[of _ "\<lambda>_. VNu"]) simp
    qed
  qed
next
  case (vInter \<Gamma> t A B)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "t = dbsub s \<sigma>" and nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : VNu"
    from vInter.IH(1) e nu obtain \<Delta>1 where
      a1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta>1 i" and a2: "\<Delta>1 \<turnstile>\<^sub>v s : A" by blast
    from vInter.IH(2) e nu obtain \<Delta>2 where
      b1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta>2 i" and b2: "\<Delta>2 \<turnstile>\<^sub>v s : B" by blast
    let ?D = "cmeet \<Delta>1 \<Delta>2"
    have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : ?D i" using a1 b1 by (simp add: cmeet_def vty_of.vInter)
    have d1: "?D \<turnstile>\<^sub>v s : A" using a2 cle_meet1 by (rule ctx_mono)
    have d2: "?D \<turnstile>\<^sub>v s : B" using b2 cle_meet2 by (rule ctx_mono)
    from d1 d2 have d: "?D \<turnstile>\<^sub>v s : VInter A B" by (rule vty_of.vInter)
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>v \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>v s : VInter A B"
      by (rule exI[of _ ?D]) (rule conjI[OF hs d])
  qed
next
  case (vSub \<Gamma> t A B)
  then show ?case by (blast intro: vty_of.vSub)
qed

lemma expand_beta:
  assumes "\<Gamma> \<turnstile>\<^sub>v subst s u 0 : A" "\<Gamma> \<turnstile>\<^sub>v u : VNu"
  shows "\<Gamma> \<turnstile>\<^sub>v DApp (DAbs s) u : A"
proof -
  from assms have h: "\<Gamma> \<turnstile>\<^sub>v dbsub s (ins 0 u) : A" by (simp add: subst_sub)
  have nu: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v ins 0 u i : VNu"
  proof
    fix i show "\<Gamma> \<turnstile>\<^sub>v ins 0 u i : VNu"
      using assms(2) by (cases i) (auto simp: ins_def intro: vty_of.vVar vty_of.vSub vs_nu)
  qed
  from expand_aux[OF h] nu obtain \<Delta> where
    h1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>v ins 0 u i : \<Delta> i" and h2: "\<Delta> \<turnstile>\<^sub>v s : A" by blast
  have h3: "\<forall>i. \<Gamma> i \<le>\<^sub>v \<Delta> (Suc i)"
  proof
    fix i
    have "\<Gamma> \<turnstile>\<^sub>v ins 0 u (Suc i) : \<Delta> (Suc i)" using h1 by blast
    then have "\<Gamma> \<turnstile>\<^sub>v DVar i : \<Delta> (Suc i)" by (simp add: ins_def)
    then show "\<Gamma> i \<le>\<^sub>v \<Delta> (Suc i)" by (rule gen_var)
  qed
  have "cle (\<Delta> 0 ## \<Gamma>) \<Delta>"
    unfolding cle_def
  proof
    fix i show "(\<Delta> 0 ## \<Gamma>) i \<le>\<^sub>v \<Delta> i" using h3 by (cases i) (simp_all add: vs_refl)
  qed
  with h2 have "(\<Delta> 0 ## \<Gamma>) \<turnstile>\<^sub>v s : A" by (rule ctx_mono)
  then have "\<Gamma> \<turnstile>\<^sub>v DAbs s : VArr (\<Delta> 0) A" by (rule vty_of.vAbs)
  moreover have "\<Gamma> \<turnstile>\<^sub>v u : \<Delta> 0"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>v ins 0 u 0 : \<Delta> 0" using h1 by blast
    then show ?thesis by (simp add: ins_def)
  qed
  ultimately show ?thesis by (rule vty_of.vApp)
qed

text \<open>Fireballs are typable; inert terms have every type.\<close>

lemma fb_typable:
  "(dinert i \<longrightarrow> (\<forall>A. \<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v i : A)) \<and> (dfb i \<longrightarrow> (\<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v i : VNu))"
proof (induction i)
  case (DVar i)
  have "\<forall>A. \<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v DVar i : A"
  proof
    fix A show "\<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v DVar i : A" by (rule exI[of _ "\<lambda>_. A"]) (rule vty_of.vVar, simp)
  qed
  then show ?case by blast
next
  case (DAbs s)
  have "(\<lambda>_. VNu) \<turnstile>\<^sub>v DAbs s : VNu" by (rule vty_of.vNu)
  then show ?case by auto
next
  case (DApp s t)
  have inert: "\<forall>A. \<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v DApp s t : A" if a: "dinert s" "dfb t"
  proof
    fix A
    from DApp.IH(2) a(2) obtain \<Gamma>2 where g2: "\<Gamma>2 \<turnstile>\<^sub>v t : VNu" by blast
    from DApp.IH(1) a(1) obtain \<Gamma>1 where g1: "\<Gamma>1 \<turnstile>\<^sub>v s : VArr VNu A" by blast
    have "cmeet \<Gamma>1 \<Gamma>2 \<turnstile>\<^sub>v s : VArr VNu A" using g1 cle_meet1 by (rule ctx_mono)
    moreover have "cmeet \<Gamma>1 \<Gamma>2 \<turnstile>\<^sub>v t : VNu" using g2 cle_meet2 by (rule ctx_mono)
    ultimately show "\<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>v DApp s t : A" by (blast intro: vty_of.vApp)
  qed
  show ?case using inert by (auto simp: dinert_DApp_iff dfb_DApp_iff)
qed

lemma refine_fb:
  assumes "dfb u"
  shows "\<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v u : VNu"
proof -
  from fb_typable assms obtain \<Delta> where "\<Delta> \<turnstile>\<^sub>v u : VNu" by blast
  then have "cmeet \<Gamma> \<Delta> \<turnstile>\<^sub>v u : VNu" using cle_meet2 by (rule ctx_mono)
  then show ?thesis using cle_meet1 by blast
qed

lemma expand_app:
  assumes "\<Gamma> \<turnstile>\<^sub>v r : A"
    and IH1: "\<And>\<Gamma> C. \<Gamma> \<turnstile>\<^sub>v s' : C \<Longrightarrow> \<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v s : C"
    and IH2: "\<And>\<Gamma> C. \<Gamma> \<turnstile>\<^sub>v t' : C \<Longrightarrow> \<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v t : C"
  shows "r = DApp s' t' \<longrightarrow> (\<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v DApp s t : A)"
using assms(1)
proof (induction rule: vty_of.induct)
  case (vApp \<Gamma> p A B q)
  show ?case
  proof
    assume e: "DApp p q = DApp s' t'"
    with vApp.hyps have hp: "\<Gamma> \<turnstile>\<^sub>v s' : VArr A B" and hq: "\<Gamma> \<turnstile>\<^sub>v t' : A" by simp_all
    from IH1[OF hp] obtain \<Gamma>1 where c1: "cle \<Gamma>1 \<Gamma>" and d1: "\<Gamma>1 \<turnstile>\<^sub>v s : VArr A B" by blast
    from IH2[OF hq] obtain \<Gamma>2 where c2: "cle \<Gamma>2 \<Gamma>" and d2: "\<Gamma>2 \<turnstile>\<^sub>v t : A" by blast
    have "cmeet \<Gamma>1 \<Gamma>2 \<turnstile>\<^sub>v DApp s t : B"
      using ctx_mono[OF d1 cle_meet1] ctx_mono[OF d2 cle_meet2] by (rule vty_of.vApp)
    moreover have "cle (cmeet \<Gamma>1 \<Gamma>2) \<Gamma>" using cle_trans[OF cle_meet1 c1] .
    ultimately show "\<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v DApp s t : B" by blast
  qed
next
  case (vInter \<Gamma> t0 A B)
  show ?case
  proof
    assume e: "t0 = DApp s' t'"
    from vInter.IH(1) e obtain \<Gamma>1 where c1: "cle \<Gamma>1 \<Gamma>" and d1: "\<Gamma>1 \<turnstile>\<^sub>v DApp s t : A" by blast
    from vInter.IH(2) e obtain \<Gamma>2 where c2: "cle \<Gamma>2 \<Gamma>" and d2: "\<Gamma>2 \<turnstile>\<^sub>v DApp s t : B" by blast
    have "cmeet \<Gamma>1 \<Gamma>2 \<turnstile>\<^sub>v DApp s t : VInter A B"
      using ctx_mono[OF d1 cle_meet1] ctx_mono[OF d2 cle_meet2] by (rule vty_of.vInter)
    moreover have "cle (cmeet \<Gamma>1 \<Gamma>2) \<Gamma>" using cle_trans[OF cle_meet1 c1] .
    ultimately show "\<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v DApp s t : VInter A B" by blast
  qed
next
  case (vSub \<Gamma> t0 A B) then show ?case by (blast intro: vty_of.vSub)
qed simp_all

lemma subject_expansion:
  assumes "t \<rightarrow>\<^sub>f t'"
  shows "\<Gamma> \<turnstile>\<^sub>v t' : A \<Longrightarrow> \<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v t : A"
using assms
proof (induction arbitrary: \<Gamma> A rule: vred.induct)
  case (vbeta u s)
  from refine_fb[OF vbeta.hyps] obtain \<Gamma>' where c: "cle \<Gamma>' \<Gamma>" and nu: "\<Gamma>' \<turnstile>\<^sub>v u : VNu" by blast
  have "\<Gamma>' \<turnstile>\<^sub>v subst s u 0 : A" using vbeta.prems c by (rule ctx_mono)
  then have "\<Gamma>' \<turnstile>\<^sub>v DApp (DAbs s) u : A" using nu by (rule expand_beta)
  then show ?case using c by blast
next
  case (vappL s s' t)
  have "\<And>\<Gamma> C. \<Gamma> \<turnstile>\<^sub>v t : C \<Longrightarrow> \<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v t : C" using cle_refl by blast
  from expand_app[OF vappL.prems vappL.IH this] show ?case by blast
next
  case (vappR s t t')
  have "\<And>\<Gamma> C. \<Gamma> \<turnstile>\<^sub>v s : C \<Longrightarrow> \<exists>\<Gamma>'. cle \<Gamma>' \<Gamma> \<and> \<Gamma>' \<turnstile>\<^sub>v s : C" using cle_refl by blast
  from expand_app[OF vappR.prems this vappR.IH] show ?case by blast
qed

subsection \<open>Completeness and the classical theorem\<close>

theorem classical_complete:
  assumes "lam_VN t"
  shows "\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>v t : A"
proof -
  from assms obtain u where r: "vred\<^sup>*\<^sup>* t u" and nf: "normal vred u" by (auto simp: lam_VN_def)
  from fb_typable normal_dfb[OF nf] have "\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>v u : A" by blast
  with r show ?thesis
  proof (induction rule: converse_rtranclp_induct)
    case base then show ?case by blast
  next
    case (step y z)
    then show ?case using subject_expansion by blast
  qed
qed

theorem classical_VN:
  "lam_VN t \<longleftrightarrow> (\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>v t : A)"
  using classical_complete classical_sound by blast

end
