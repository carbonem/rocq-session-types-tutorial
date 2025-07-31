(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
From Coq Require Import FunctionalExtensionality.
Require Import free_names types semantics syntax fintype core linearity_predicate.


Definition env (n:nat) := ch n -> sType.

Definition update {n : nat} (e : env n) (x : ch n) (T : sType) : 
  env n := fun y => if (x==y) then T else e y.

Lemma update_others {n : nat}: forall c x T (Delta : env n),
    c <> x -> update Delta x T c = Delta c. 
Proof. 
  move => c x T Delta H.
  rewrite/update. 
  by case: ifP => // => /eqP => Hyp; subst.
Qed. 

Lemma update_swap {n : nat}: forall x T1 y T2 (Delta : env n),
    x<>y -> update (update Delta x T1) y T2 = 
              update (update Delta y T2) x T1. 
Proof.
  move => x T1 y T2 Delta H.
  apply/functional_extensionality => x0.
  rewrite/update.
  case: ifP.
  - move/eqP => H'; subst. 
    case: ifP => //.
    move/eqP => //.
  - move/eqP => H'. 
    case: ifP => //.
Qed. 


Definition shift_env {n : nat} (T : sType) (e : env n) : env n.+1 :=
  fun x => match x with
           | var_ch None => T
           | var_ch (Some i) => e (var_ch i)
           end.

Lemma update_var_zero {n : nat}: forall T1 T2 Delta,
    (update (shift_env T1 Delta) (n.+2__ch var_zero) T2) 
    = (shift_env T2 Delta). 
Proof.
  move => T1 T2 Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
  destruct f => //.
Qed. 

Lemma update_var_one {n : nat}: forall T1 T2 T Delta,
    (update (shift_env T1 (shift_env T2 Delta)) (n.+2__ch var_one) T) 
    = (shift_env T1 (shift_env T Delta)). 
Proof.
  move => T1 T2 T Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
  destruct f => //.
  destruct f => //.
Qed. 

Lemma update_var_two {n : nat}: forall T1 T2 T3 T Delta,
    (update (shift_env T1 (shift_env T2 (shift_env T3 Delta)))
       (n.+3__ch var_two) T) 
    = (shift_env T1 (shift_env T2 (shift_env T Delta))). 
Proof.
  move => T1 T2 T3 T Delta. 
  apply/functional_extensionality => x0.
  destruct x0 => //.
  destruct f => //.
  destruct f => //.
  destruct f => //.
Qed. 

Lemma shift_env_update {n : nat}: forall i T1 T2 (Delta : env n),
    shift_env T1 (update Delta (var_ch i) T2) = 
      update (shift_env T1 Delta) (var_ch (shift i)) T2. 
Proof. 
  move => i T1 T2 Delta.
  apply/functional_extensionality => x0.
  rewrite/shift_env/update => /=.
  case: ifP. 
  - move/eqP => <- /=.
    case: ifP => //.
    move/eqP => //.
  - destruct x0 => //.
    destruct f => //.
    move/eqP.
    case: ifP => //.
    move/eqP.
    case => ->.
    case => //.
Qed. 

(* Relation between typing environments *) 
Definition ltc {n m} (Delta: env n) (Gamma: env m) (sigma : fin n -> ch m) P := 
  forall i, free_in (var_ch i) P -> Delta (var_ch i) = Gamma (sigma i).

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
      (up_ch_ch (up_ch_ch sigma))
      P.
Proof.
  move => T1 T2 Delta Gamma sigma P. 
  rewrite/ltc/shift_env => H i Hyp.
  destruct i => //=. 
  destruct f => //.
  rewrite H => //=. 
  rewrite/up_ch_ch/funcomp => /=. 
  destruct (sigma f) => //.
Qed.

Lemma ltc_ParPL {n m}: forall {Delta: env n} {Gamma: env m} sigma P Q, 
    ltc Delta Gamma sigma (ParP P Q) -> ltc Delta Gamma sigma P.
Proof.
  move => Delta Gamma sigma P Q H. 
  rewrite/ltc => i H'.
  by apply/H => /=; left.
Qed. 

Lemma ltc_ParPR {n m}: forall {Delta: env n} {Gamma: env m} sigma P Q, 
    ltc Delta Gamma sigma (ParP P Q) -> ltc Delta Gamma sigma Q.
Proof.
  move => Delta Gamma sigma P Q H. 
  rewrite/ltc => i H'.
  by apply/H => /=; right.
Qed. 

Lemma ltc_InSP {n m}: forall T {Delta: env n} {Gamma: env m} sigma x P, 
    ltc Delta Gamma sigma (InSP x P) -> 
    ltc (shift_env T Delta) (shift_env T Gamma) (up_ch_ch sigma) P.
Proof.
  move => T Delta Gamma sigma x P.
  rewrite/ltc/shift_env => H i Hyp.  
  destruct i => //=. 
  rewrite H => /=.
  rewrite/funcomp. 
  by destruct (sigma f).
  by right. 
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
    ltc (shift_env T Delta)  Delta (scons x n __ch) P.
Proof.
  move => x T Delta P H.
  rewrite/shift_env/ltc => k'.
  destruct k' => //=.
Qed. 

Definition swap_env {n : nat} (Delta : env n) j k := 
  fun i => if i == j then Delta k else if i == k then Delta j else Delta i.

Lemma ltc_swap {n : nat} : forall j k Delta Gamma (P : proc n), 
    Gamma = (swap_env Delta (var_ch j) (var_ch k)) -> 
    ltc Delta Gamma (swap_ch j k) P.
Proof. 
  rewrite/swap_env/swap_ch => j k Delta Gamma P H1 i H2; subst.
  case: ifP.
  - move/eqP; case.
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
    move/eqP; case => //.
Qed. 

(* Injectivity and update *) 
Lemma ltc_update {k k'}: forall n T {Delta: env k} {Gamma: env k'} P sigma,
    free_in (var_ch n) P -> 
    injectiveS P sigma -> 
    ltc Delta Gamma sigma P -> 
    ltc (update Delta (var_ch n) T) (update Gamma (sigma n) T) sigma P.
Proof. 
  move => n T Delta Gamma P sigma Hfree H1.
  rewrite/ltc => H2 i. 
  rewrite/update. 
  case: ifP => /eqP.
  + case => Hyp; subst. 
    case: ifP => /eqP => //.
  + move => Hyp1 Hyp2.
    have fact : n <> i. 
    move:Hyp1.
    by apply/contra_not => ->.
    case : ifP.
    move/eqP => /H1. 
    move => H.
    apply fact in H => //.
    move => _.
    rewrite H2 => //.
Qed.

