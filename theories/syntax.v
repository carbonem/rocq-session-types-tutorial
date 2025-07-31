Require Import core fintype.
Require Import Setoid Morphisms Relation_Definitions.
From HB Require Import structures.

Module Core.

Inductive ch (n_ch : nat) : Type :=
    var_ch : fin n_ch -> ch n_ch.

Definition subst_ch {m_ch : nat} {n_ch : nat}
  (sigma_ch : fin m_ch -> ch n_ch) (s : ch m_ch) : ch n_ch :=
  match s with
  | var_ch _ s0 => sigma_ch s0
  end.


Lemma up_ch_ch {m : nat} {n_ch : nat} (sigma : fin m -> ch n_ch) :
  fin (S m) -> ch (S n_ch).
Proof.
exact (scons (var_ch (S n_ch) var_zero)
         (funcomp (subst_ch (funcomp (var_ch _) shift)) sigma)).
Defined.

Lemma up_list_ch_ch (p : nat) {m : nat} {n_ch : nat}
  (sigma : fin m -> ch n_ch) : fin (plus p m) -> ch (plus p n_ch).
Proof.
exact (scons_p p (funcomp (var_ch (plus p n_ch)) (zero_p p))
         (funcomp (subst_ch (funcomp (var_ch _) (shift_p p))) sigma)).
Defined.

Lemma upId_ch_ch {m_ch : nat} (sigma : fin m_ch -> ch m_ch)
  (Eq : forall x, sigma x = var_ch m_ch x) :
  forall x, up_ch_ch sigma x = var_ch (S m_ch) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_ch (funcomp (var_ch _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_ch_ch {p : nat} {m_ch : nat} (sigma : fin m_ch -> ch m_ch)
  (Eq : forall x, sigma x = var_ch m_ch x) :
  forall x, up_list_ch_ch p sigma x = var_ch (plus p m_ch) x.
Proof.
exact (fun n =>
       scons_p_eta (var_ch (plus p m_ch))
         (fun n => ap (subst_ch (funcomp (var_ch _) (shift_p p))) (Eq n))
         (fun n => eq_refl)).
Qed.

Definition idSubst_ch {m_ch : nat} (sigma_ch : fin m_ch -> ch m_ch)
  (Eq_ch : forall x, sigma_ch x = var_ch m_ch x) (s : ch m_ch) :
  subst_ch sigma_ch s = s := match s with
                             | var_ch _ s0 => Eq_ch s0
                             end.

Lemma upExt_ch_ch {m : nat} {n_ch : nat} (sigma : fin m -> ch n_ch)
  (tau : fin m -> ch n_ch) (Eq : forall x, sigma x = tau x) :
  forall x, up_ch_ch sigma x = up_ch_ch tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (subst_ch (funcomp (var_ch _) shift)) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_ch_ch {p : nat} {m : nat} {n_ch : nat}
  (sigma : fin m -> ch n_ch) (tau : fin m -> ch n_ch)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ch_ch p sigma x = up_list_ch_ch p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (subst_ch (funcomp (var_ch _) (shift_p p))) (Eq n))).
Qed.

Definition ext_ch {m_ch : nat} {n_ch : nat} (sigma_ch : fin m_ch -> ch n_ch)
  (tau_ch : fin m_ch -> ch n_ch) (Eq_ch : forall x, sigma_ch x = tau_ch x)
  (s : ch m_ch) : subst_ch sigma_ch s = subst_ch tau_ch s :=
  match s with
  | var_ch _ s0 => Eq_ch s0
  end.

Definition compSubstSubst_ch {k_ch : nat} {l_ch : nat} {m_ch : nat}
  (sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch)
  (theta_ch : fin m_ch -> ch l_ch)
  (Eq_ch : forall x, funcomp (subst_ch tau_ch) sigma_ch x = theta_ch x)
  (s : ch m_ch) :
  subst_ch tau_ch (subst_ch sigma_ch s) = subst_ch theta_ch s :=
  match s with
  | var_ch _ s0 => Eq_ch s0
  end.

Lemma up_subst_subst_ch_ch {k : nat} {l_ch : nat} {m_ch : nat}
  (sigma : fin k -> ch l_ch) (tau_ch : fin l_ch -> ch m_ch)
  (theta : fin k -> ch m_ch)
  (Eq : forall x, funcomp (subst_ch tau_ch) sigma x = theta x) :
  forall x,
  funcomp (subst_ch (up_ch_ch tau_ch)) (up_ch_ch sigma) x = up_ch_ch theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compSubstSubst_ch (funcomp (var_ch _) shift) (up_ch_ch tau_ch)
                (funcomp (up_ch_ch tau_ch) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstSubst_ch tau_ch (funcomp (var_ch _) shift)
                      (funcomp (subst_ch (funcomp (var_ch _) shift)) tau_ch)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (subst_ch (funcomp (var_ch _) shift)) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_ch_ch {p : nat} {k : nat} {l_ch : nat} {m_ch : nat}
  (sigma : fin k -> ch l_ch) (tau_ch : fin l_ch -> ch m_ch)
  (theta : fin k -> ch m_ch)
  (Eq : forall x, funcomp (subst_ch tau_ch) sigma x = theta x) :
  forall x,
  funcomp (subst_ch (up_list_ch_ch p tau_ch)) (up_list_ch_ch p sigma) x =
  up_list_ch_ch p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_ch (plus p l_ch)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x =>
             scons_p_head' _
               (fun z => subst_ch (funcomp (var_ch _) (shift_p p)) _) x)
            (fun n =>
             eq_trans
               (compSubstSubst_ch (funcomp (var_ch _) (shift_p p))
                  (up_list_ch_ch p tau_ch)
                  (funcomp (up_list_ch_ch p tau_ch) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstSubst_ch tau_ch
                        (funcomp (var_ch _) (shift_p p)) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (subst_ch (funcomp (var_ch _) (shift_p p))) (Eq n)))))).
Qed.

Lemma substSubst_ch {k_ch : nat} {l_ch : nat} {m_ch : nat}
  (sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch)
  (s : ch m_ch) :
  subst_ch tau_ch (subst_ch sigma_ch s) =
  subst_ch (funcomp (subst_ch tau_ch) sigma_ch) s.
Proof.
exact (compSubstSubst_ch sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ch_pointwise {k_ch : nat} {l_ch : nat} {m_ch : nat}
  (sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch) :
  pointwise_relation _ eq (funcomp (subst_ch tau_ch) (subst_ch sigma_ch))
    (subst_ch (funcomp (subst_ch tau_ch) sigma_ch)).
Proof.
exact (fun s => compSubstSubst_ch sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ch {m_ch : nat} (s : ch m_ch) : subst_ch (var_ch m_ch) s = s.
Proof.
exact (idSubst_ch (var_ch m_ch) (fun n => eq_refl) s).
Qed.

Lemma instId'_ch_pointwise {m_ch : nat} :
  pointwise_relation _ eq (subst_ch (var_ch m_ch)) id.
Proof.
exact (fun s => idSubst_ch (var_ch m_ch) (fun n => eq_refl) s).
Qed.

Lemma varL'_ch {m_ch : nat} {n_ch : nat} (sigma_ch : fin m_ch -> ch n_ch)
  (x : fin m_ch) : subst_ch sigma_ch (var_ch m_ch x) = sigma_ch x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ch_pointwise {m_ch : nat} {n_ch : nat}
  (sigma_ch : fin m_ch -> ch n_ch) :
  pointwise_relation _ eq (funcomp (subst_ch sigma_ch) (var_ch m_ch))
    sigma_ch.
Proof.
exact (fun x => eq_refl).
Qed.

Inductive proc (n_ch : nat) : Type :=
  | EndP : proc n_ch
  | WaitP : ch n_ch -> proc n_ch -> proc n_ch
  | CloseP : ch n_ch -> proc n_ch -> proc n_ch
  | ResP : proc (S (S n_ch)) -> proc n_ch
  | ParP : proc n_ch -> proc n_ch -> proc n_ch
  | InSP : ch n_ch -> proc (S n_ch) -> proc n_ch
  | DelP : ch n_ch -> ch n_ch -> proc n_ch -> proc n_ch.


Lemma congr_EndP {m_ch : nat} : EndP m_ch = EndP m_ch.
Proof.
exact (eq_refl).
Qed.

Lemma congr_WaitP {m_ch : nat} {s0 : ch m_ch} {s1 : proc m_ch} {t0 : ch m_ch}
  {t1 : proc m_ch} (H0 : s0 = t0) (H1 : s1 = t1) :
  WaitP m_ch s0 s1 = WaitP m_ch t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => WaitP m_ch x s1) H0))
         (ap (fun x => WaitP m_ch t0 x) H1)).
Qed.

Lemma congr_CloseP {m_ch : nat} {s0 : ch m_ch} {s1 : proc m_ch}
  {t0 : ch m_ch} {t1 : proc m_ch} (H0 : s0 = t0) (H1 : s1 = t1) :
  CloseP m_ch s0 s1 = CloseP m_ch t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => CloseP m_ch x s1) H0))
         (ap (fun x => CloseP m_ch t0 x) H1)).
Qed.

Lemma congr_ResP {m_ch : nat} {s0 : proc (S (S m_ch))}
  {t0 : proc (S (S m_ch))} (H0 : s0 = t0) : ResP m_ch s0 = ResP m_ch t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ResP m_ch x) H0)).
Qed.

Lemma congr_ParP {m_ch : nat} {s0 : proc m_ch} {s1 : proc m_ch}
  {t0 : proc m_ch} {t1 : proc m_ch} (H0 : s0 = t0) (H1 : s1 = t1) :
  ParP m_ch s0 s1 = ParP m_ch t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ParP m_ch x s1) H0))
         (ap (fun x => ParP m_ch t0 x) H1)).
Qed.

Lemma congr_InSP {m_ch : nat} {s0 : ch m_ch} {s1 : proc (S m_ch)}
  {t0 : ch m_ch} {t1 : proc (S m_ch)} (H0 : s0 = t0) (H1 : s1 = t1) :
  InSP m_ch s0 s1 = InSP m_ch t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => InSP m_ch x s1) H0))
         (ap (fun x => InSP m_ch t0 x) H1)).
Qed.

Lemma congr_DelP {m_ch : nat} {s0 : ch m_ch} {s1 : ch m_ch} {s2 : proc m_ch}
  {t0 : ch m_ch} {t1 : ch m_ch} {t2 : proc m_ch} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) : DelP m_ch s0 s1 s2 = DelP m_ch t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => DelP m_ch x s1 s2) H0))
            (ap (fun x => DelP m_ch t0 x s2) H1))
         (ap (fun x => DelP m_ch t0 t1 x) H2)).
Qed.

Fixpoint subst_proc {m_ch : nat} {n_ch : nat}
(sigma_ch : fin m_ch -> ch n_ch) (s : proc m_ch) {struct s} : proc n_ch :=
  match s with
  | EndP _ => EndP n_ch
  | WaitP _ s0 s1 =>
      WaitP n_ch (subst_ch sigma_ch s0) (subst_proc sigma_ch s1)
  | CloseP _ s0 s1 =>
      CloseP n_ch (subst_ch sigma_ch s0) (subst_proc sigma_ch s1)
  | ResP _ s0 => ResP n_ch (subst_proc (up_ch_ch (up_ch_ch sigma_ch)) s0)
  | ParP _ s0 s1 =>
      ParP n_ch (subst_proc sigma_ch s0) (subst_proc sigma_ch s1)
  | InSP _ s0 s1 =>
      InSP n_ch (subst_ch sigma_ch s0) (subst_proc (up_ch_ch sigma_ch) s1)
  | DelP _ s0 s1 s2 =>
      DelP n_ch (subst_ch sigma_ch s0) (subst_ch sigma_ch s1)
        (subst_proc sigma_ch s2)
  end.

Fixpoint idSubst_proc {m_ch : nat} (sigma_ch : fin m_ch -> ch m_ch)
(Eq_ch : forall x, sigma_ch x = var_ch m_ch x) (s : proc m_ch) {struct s} :
subst_proc sigma_ch s = s :=
  match s with
  | EndP _ => congr_EndP
  | WaitP _ s0 s1 =>
      congr_WaitP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | CloseP _ s0 s1 =>
      congr_CloseP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | ResP _ s0 =>
      congr_ResP
        (idSubst_proc (up_ch_ch (up_ch_ch sigma_ch))
           (upId_ch_ch _ (upId_ch_ch _ Eq_ch)) s0)
  | ParP _ s0 s1 =>
      congr_ParP (idSubst_proc sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | InSP _ s0 s1 =>
      congr_InSP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc (up_ch_ch sigma_ch) (upId_ch_ch _ Eq_ch) s1)
  | DelP _ s0 s1 s2 =>
      congr_DelP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_ch sigma_ch Eq_ch s1) (idSubst_proc sigma_ch Eq_ch s2)
  end.

Fixpoint ext_proc {m_ch : nat} {n_ch : nat} (sigma_ch : fin m_ch -> ch n_ch)
(tau_ch : fin m_ch -> ch n_ch) (Eq_ch : forall x, sigma_ch x = tau_ch x)
(s : proc m_ch) {struct s} : subst_proc sigma_ch s = subst_proc tau_ch s :=
  match s with
  | EndP _ => congr_EndP
  | WaitP _ s0 s1 =>
      congr_WaitP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | CloseP _ s0 s1 =>
      congr_CloseP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | ResP _ s0 =>
      congr_ResP
        (ext_proc (up_ch_ch (up_ch_ch sigma_ch)) (up_ch_ch (up_ch_ch tau_ch))
           (upExt_ch_ch _ _ (upExt_ch_ch _ _ Eq_ch)) s0)
  | ParP _ s0 s1 =>
      congr_ParP (ext_proc sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | InSP _ s0 s1 =>
      congr_InSP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc (up_ch_ch sigma_ch) (up_ch_ch tau_ch)
           (upExt_ch_ch _ _ Eq_ch) s1)
  | DelP _ s0 s1 s2 =>
      congr_DelP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_ch sigma_ch tau_ch Eq_ch s1) (ext_proc sigma_ch tau_ch Eq_ch s2)
  end.

Fixpoint compSubstSubst_proc {k_ch : nat} {l_ch : nat} {m_ch : nat}
(sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch)
(theta_ch : fin m_ch -> ch l_ch)
(Eq_ch : forall x, funcomp (subst_ch tau_ch) sigma_ch x = theta_ch x)
(s : proc m_ch) {struct s} :
subst_proc tau_ch (subst_proc sigma_ch s) = subst_proc theta_ch s :=
  match s with
  | EndP _ => congr_EndP
  | WaitP _ s0 s1 =>
      congr_WaitP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | CloseP _ s0 s1 =>
      congr_CloseP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | ResP _ s0 =>
      congr_ResP
        (compSubstSubst_proc (up_ch_ch (up_ch_ch sigma_ch))
           (up_ch_ch (up_ch_ch tau_ch)) (up_ch_ch (up_ch_ch theta_ch))
           (up_subst_subst_ch_ch _ _ _ (up_subst_subst_ch_ch _ _ _ Eq_ch)) s0)
  | ParP _ s0 s1 =>
      congr_ParP (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | InSP _ s0 s1 =>
      congr_InSP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc (up_ch_ch sigma_ch) (up_ch_ch tau_ch)
           (up_ch_ch theta_ch) (up_subst_subst_ch_ch _ _ _ Eq_ch) s1)
  | DelP _ s0 s1 s2 =>
      congr_DelP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s1)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s2)
  end.

Lemma substSubst_proc {k_ch : nat} {l_ch : nat} {m_ch : nat}
  (sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch)
  (s : proc m_ch) :
  subst_proc tau_ch (subst_proc sigma_ch s) =
  subst_proc (funcomp (subst_ch tau_ch) sigma_ch) s.
Proof.
exact (compSubstSubst_proc sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc_pointwise {k_ch : nat} {l_ch : nat} {m_ch : nat}
  (sigma_ch : fin m_ch -> ch k_ch) (tau_ch : fin k_ch -> ch l_ch) :
  pointwise_relation _ eq (funcomp (subst_proc tau_ch) (subst_proc sigma_ch))
    (subst_proc (funcomp (subst_ch tau_ch) sigma_ch)).
Proof.
exact (fun s => compSubstSubst_proc sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma instId'_proc {m_ch : nat} (s : proc m_ch) :
  subst_proc (var_ch m_ch) s = s.
Proof.
exact (idSubst_proc (var_ch m_ch) (fun n => eq_refl) s).
Qed.

Lemma instId'_proc_pointwise {m_ch : nat} :
  pointwise_relation _ eq (subst_proc (var_ch m_ch)) id.
Proof.
exact (fun s => idSubst_proc (var_ch m_ch) (fun n => eq_refl) s).
Qed.

Class Up_proc X Y :=
    up_proc : X -> Y.

Class Up_ch X Y :=
    up_ch : X -> Y.

#[global]
Instance Subst_proc  {m_ch n_ch : nat}: (Subst1 _ _ _) :=
 (@subst_proc m_ch n_ch).

#[global]
Instance Up_ch_ch  {m n_ch : nat}: (Up_ch _ _) := (@up_ch_ch m n_ch).

#[global]
Instance Subst_ch  {m_ch n_ch : nat}: (Subst1 _ _ _) := (@subst_ch m_ch n_ch).

#[global]
Instance VarInstance_ch  {n_ch : nat}: (Var _ _) := (@var_ch n_ch).

Notation "[ sigma_ch ]" := (subst_proc sigma_ch)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ch ]" := (subst_proc sigma_ch s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__proc" := up_proc (only printing)  : subst_scope.

Notation "↑__ch" := up_ch_ch (only printing)  : subst_scope.

Notation "[ sigma_ch ]" := (subst_ch sigma_ch)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ch ]" := (subst_ch sigma_ch s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ch" := up_ch (only printing)  : subst_scope.

Notation "'var'" := var_ch ( at level 1, only printing)  : subst_scope.

Notation "x '__ch'" := (@ids _ _ VarInstance_ch x)
( at level 5, format "x __ch", only printing)  : subst_scope.

Notation "x '__ch'" := (var_ch x) ( at level 5, format "x __ch")  :
subst_scope.

#[global]
Instance subst_proc_morphism  {m_ch : nat} {n_ch : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_proc m_ch n_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s t Eq_st =>
       eq_ind s (fun t' => subst_proc f_ch s = subst_proc g_ch t')
         (ext_proc f_ch g_ch Eq_ch s) t Eq_st).
Qed.

#[global]
Instance subst_proc_morphism2  {m_ch : nat} {n_ch : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_proc m_ch n_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s => ext_proc f_ch g_ch Eq_ch s).
Qed.

#[global]
Instance subst_ch_morphism  {m_ch : nat} {n_ch : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ch m_ch n_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s t Eq_st =>
       eq_ind s (fun t' => subst_ch f_ch s = subst_ch g_ch t')
         (ext_ch f_ch g_ch Eq_ch s) t Eq_st).
Qed.

#[global]
Instance subst_ch_morphism2  {m_ch : nat} {n_ch : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ch m_ch n_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s => ext_ch f_ch g_ch Eq_ch s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ch, Var, ids, Subst_ch, Subst1,
                      subst1, Up_ch_ch, Up_ch, up_ch, Subst_proc, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ch, Var, ids,
                                            Subst_ch, Subst1, subst1,
                                            Up_ch_ch, Up_ch, up_ch,
                                            Subst_proc, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_proc_pointwise
                 | progress setoid_rewrite substSubst_proc
                 | progress setoid_rewrite substSubst_ch_pointwise
                 | progress setoid_rewrite substSubst_ch
                 | progress setoid_rewrite instId'_proc_pointwise
                 | progress setoid_rewrite instId'_proc
                 | progress setoid_rewrite varL'_ch_pointwise
                 | progress setoid_rewrite varL'_ch
                 | progress setoid_rewrite instId'_ch_pointwise
                 | progress setoid_rewrite instId'_ch
                 | progress unfold up_list_ch_ch, up_ch_ch, up_ren
                 | progress cbn[subst_proc subst_ch]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ch, Var, ids, Subst_ch, Subst1, subst1,
                  Up_ch_ch, Up_ch, up_ch, Subst_proc, Subst1, subst1 
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.

End Core.

Module Extra.

Import
Core.

Arguments DelP {n_ch}.

Arguments InSP {n_ch}.

Arguments ParP {n_ch}.

Arguments ResP {n_ch}.

Arguments CloseP {n_ch}.

Arguments WaitP {n_ch}.

Arguments EndP {n_ch}.

Arguments var_ch {n_ch}.

#[global]Hint Opaque subst_proc: rewrite.

#[global]Hint Opaque subst_ch: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.
