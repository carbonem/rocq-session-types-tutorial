From mathcomp Require Import all_ssreflect.
From Coq Require Import FunctionalExtensionality.
Require Import free_names types synsem.

Section TotalMap.
  Variables (K : eqType) (A : Type).

  Definition total_map := K -> A.
  
  Definition t_update (m : total_map) (x : K) (v : A) : total_map :=
    fun y => if y == x then v else m y.
  
  Lemma t_update_others (m : total_map) x y v :
    y <> x -> t_update m x v y = m y.
  Proof. move=> Hyx; rewrite /t_update. case eqP => //=. Qed.

  Theorem t_update_swap : forall  (m : total_map ) v1 v2 x1 x2,
      x2 <> x1 ->
      (t_update (t_update m x2 v2) x1 v1) =
         (t_update (t_update m x1 v1) x2 v2).
      Proof.
    intros  m v1 v2 x1 x2 H.
    apply functional_extensionality. intros x3.
    rewrite /t_update => //=.
    case eqP => //=.
    intro c.
    case eqP => //=.
    intro d.
    rewrite <- d in H.
    contradiction.
  Qed.

(* Other lemmas, SF-style, unused *)
  Lemma t_update_same (m : total_map) x : t_update m x (m x) = m.
  Proof. 
    by apply/functional_extensionality  => y; rewrite /t_update; case: eqP => // ->. 
  Qed.

  Lemma t_update_eq (m : total_map) x v : t_update m x v x = v.
  Proof. by rewrite /t_update eqxx. Qed.

   Lemma t_update_shadow : forall (m : total_map ) x v1 v2,
   (t_update (t_update m x v1) x v2) =
  (t_update m x v2).
  Proof.
    intros  m x v1 v2. apply functional_extensionality. intros x'.  unfold t_update.    case: eqP => // ->. 
  Qed.
 
End TotalMap.

Notation "x '!!->' v ';' m" :=
  (t_update _ _ m x v)
    (at level 100, v at next level, right associativity).
  

Definition env (n:nat) := ch n -> sType.

Definition shift_env {n : nat} (T : sType) (e : env n) : env n.+1 := scons  T e.
  
Notation "T ::: Delta" := (shift_env T Delta) (at level 40).

Lemma update_zero {n : nat}: forall T1 T2 Delta,
    (t_update _ _ (shift_env T1 Delta) zero T2) = (@shift_env n T2 Delta). 
Proof.
  move => T1 T2 Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
Qed. 

Lemma update_one {n : nat}: forall T1 T2 T Delta,
    (t_update _ _ (shift_env T1 (shift_env T2 Delta)) one T) 
    = (shift_env T1 ( @shift_env n T Delta)). 
Proof.
  move => T1 T2 T Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
  destruct c => //.
Qed. 

Lemma update_two {n : nat}: forall T1 T2 T3 T Delta,
    (t_update _ _
       (shift_env T1 (shift_env T2 (shift_env T3 Delta))) two T)
    = (shift_env T1 (shift_env T2 (@shift_env n T Delta))). 
Proof.
  move => T1 T2 T3 T Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
  destruct c => //.
  destruct c => //.
Qed. 

Lemma shift_env_update {n : nat}: forall x T1 T2 (Delta : env n),
    shift_env T1 (t_update _ _ Delta x T2) =
      t_update _ _ (shift_env T1 Delta) (shift x) T2. 
Proof. 
  move => x T1 T2 Delta.
  apply/functional_extensionality => x0.
  rewrite/shift_env/t_update => /=.
  case: ifP. 
  - move/eqP => -> /=.
    case: ifP => //.
    move/eqP => //.
  - destruct x0 => //=.
    move/eqP => H.
    case: ifP => //.
    move/eqP => H'; subst => //.
Qed.
  
(* Relation between typing environments *) 
Definition ltc {n m} (Delta: env n) (Gamma: env m) (sigma : ch n -> ch m) P := 
  forall x, free_in x P -> Delta  x = Gamma (sigma x).

Lemma ltc_WaitP {n m}: forall {Delta: env n} {Gamma: env m} sigma x P, 
    ltc Delta Gamma sigma (WaitP x P) -> ltc Delta Gamma sigma P.
Proof.
  move => Delta Gamma sigma x P H. 
  rewrite/ltc => i H'.
  by apply/H => /= ; right.
Qed. 

Lemma ltc_CloseP {n m}: forall {Delta: env n} {Gamma: env m} sigma x P, 
    ltc Delta Gamma sigma (CloseP x P) -> ltc Delta Gamma sigma P.
Proof.
  move => Delta Gamma sigma x P H. 
  rewrite/ltc => i H'.
  by apply/H => /= ; right.
Qed. 

Lemma ltc_ResP {n m}: forall T1 T2 {Delta: env n} {Gamma: env m} sigma P, 
    ltc Delta Gamma sigma (ResP P) -> 
    ltc (shift_env T1 (shift_env T2 Delta)) 
      (shift_env T1 (shift_env T2 Gamma)) 
      (up_ch (up_ch sigma))
      P.
Proof.
  move => T1 T2 Delta Gamma sigma P. 
  rewrite/ltc/shift_env => H x Hyp.
  destruct x => //=. 
  destruct c => //=.
  rewrite H => //=. 
Qed.

Lemma ltc_ParPL {n m}: forall {Delta: env n} {Gamma: env m} sigma P Q, 
    ltc Delta Gamma sigma (ParP P Q) -> ltc Delta Gamma sigma P.
Proof.
  move => Delta Gamma sigma P Q H. 
  rewrite/ltc => x H'.
  by apply/H => /=; left.
Qed. 

Lemma ltc_ParPR {n m}: forall {Delta: env n} {Gamma: env m} sigma P Q, 
    ltc Delta Gamma sigma (ParP P Q) -> ltc Delta Gamma sigma Q.
Proof.
  move => Delta Gamma sigma P Q H. 
  rewrite/ltc => x H'.
  by apply/H => /=; right.
Qed. 

Lemma ltc_InSP {n m}: forall T {Delta: env n} {Gamma: env m} sigma x P, 
    ltc Delta Gamma sigma (InSP x P) -> 
    ltc (shift_env T Delta) (shift_env T Gamma) (up_ch sigma) P.
Proof.
  move => T Delta Gamma sigma x P H y Hyp.  
  destruct y => //.
  by apply/H; right.
Qed. 

Lemma ltc_DelP {n m}: forall {Delta: env n} {Gamma: env m} sigma x y P, 
    ltc Delta Gamma sigma (DelP x y P) -> ltc Delta Gamma sigma P.
Proof.
  move => Delta Gamma sigma x y P.
  rewrite/ltc => H i Hyp.
  by apply/H => /=; right; right. 
Qed. 

Lemma ltc_scons {n : nat} : forall x T Delta P,
    Delta x = T -> 
    @ltc n.+1 n (shift_env T Delta) Delta (scons x id_ren) P.
Proof.
  move => x T Delta P H.
  rewrite/shift_env/ltc => k'.
  destruct k' => //=.
Qed. 

Definition swap_env {n : nat} (Delta : env n) j k := 
  fun i => if i == j then Delta k else if i == k then Delta j else Delta i.

Lemma ltc_swap {n : nat} : forall x y Delta Gamma (P : proc n), 
    Gamma = (swap_env Delta x y) -> ltc Delta Gamma (swap_ch x y) P.
Proof. 
  move => x y Delta Gamma P H1 i H2; subst.
  rewrite/swap_env/swap_ch.
  case: ifP.
  - move/eqP.
    case: ifP.
    by move/eqP => -> ->.
    move/eqP => H1.
    case: ifP => //.
    by move/eqP => -> _.
  - move/eqP. 
    case: ifP.
    move/eqP => -> H1.
    case: ifP => //.
    move/eqP => //.
    move/eqP => H1.
    case: ifP => //.
    move/eqP => H3 H4.
    case: ifP => //.
    move/eqP => H; subst => //.
Qed. 

(* Injectivity and update *) 
Lemma ltc_update {k k'}: forall x T {Delta: env k} {Gamma: env k'} P sigma,
    free_in x P -> 
    injectiveS P sigma -> 
    ltc Delta Gamma sigma P -> 
    ltc (t_update _ _ Delta x T)
      (t_update _ _ Gamma (sigma x) T) sigma P.
Proof. 
  move => x T Delta Gamma P sigma Hfree H1 H2 y H. 
  rewrite/t_update. 
  case: ifP => /eqP.
  + move => Hyp; subst. 
    case: ifP => /eqP => //.
  + move => Hdiff.
    case : ifP.
    * move/eqP => /H1 => Hyp.
      move:  (Hyp H Hfree) => Hyp' => //.
    * move/eqP => Hdiff'.
      rewrite H2 => //.
Qed. 
