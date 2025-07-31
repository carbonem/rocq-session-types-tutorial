(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import core fintype syntax semantics. 
Open Scope subst_scope.

Fixpoint free_in {n : nat} (z : ch n) (P : proc n ) := 
  match P with
  | EndP       => False
  | WaitP x P  => (x = z) \/ (free_in z P)
  | CloseP x P => (x = z) \/ (free_in z P)
  | ResP P     => free_in (subst_ch (fun i => var_ch (shift (shift i))) z) P
  | ParP P Q   => (free_in z P) \/ (free_in z Q)
  | InSP x P   => (x = z) \/ 
                    (free_in (subst_ch (fun i => var_ch (shift i)) z)P)
  | DelP x y P => (x = z) \/ (y = z) \/ free_in z P
end. 

Fixpoint notfree_in {n : nat} (z : ch n) (P : proc n) :=
  match P with
  | EndP       => True
  | WaitP x P  => (x <> z) /\ (notfree_in z P)
  | CloseP x P => (x <> z) /\ (notfree_in z P)
  | ResP P     => notfree_in (subst_ch (fun i => var_ch (shift (shift i))) z) P
  | ParP P Q   => (notfree_in z P) /\ (notfree_in z Q)
  | InSP x P   => (x <> z) /\ 
                    (notfree_in (subst_ch (fun i => var_ch (shift i)) z) P)
  | DelP x y P => (x <> z) /\ (y <> z) /\ notfree_in z P
  end.

Lemma free_not_free_in {n : nat} (z : ch n) (P : proc n) : 
  ~ free_in z P <-> notfree_in z P.
Proof.
  induction P; firstorder.
  Qed.  


(* InjectiveS -- injective on a given set (as free names) *) 

Definition injectiveS {n : nat} {m : nat} (P: proc n) := 
  fun (f : fin n -> ch m) =>
    forall i j: fin n, free_in (var_ch i) P -> free_in (var_ch j) P ->
                       (f i) = (f j) -> i = j.

Lemma injectiveS_ResP {n m : nat} : forall (P : proc n.+2) (sigma : fin n -> ch m),
    injectiveS (ResP P) sigma -> injectiveS P (up_ch_ch (up_ch_ch sigma)). 
Proof. 
  move => P sigma.
  rewrite/injectiveS => H i j H1 H2.
  destruct i.
  destruct j.
  asimpl.
  destruct f.
  destruct f0 => Hyp.
  f_equal; f_equal.
  apply/H => //.
  move: Hyp.
  asimpl.
  rewrite/funcomp.
  destruct (sigma f) => //.
  destruct (sigma f0) => //.
  asimpl.
  by case => ->.
  move:Hyp.
  asimpl.
  rewrite/funcomp.
  destruct (sigma f) => //.
  asimpl.
  rewrite/scons/funcomp. 
  destruct f0 => //.
  destruct (sigma f) => //.
  asimpl.
  rewrite/scons/funcomp. 
  destruct f => //.
  destruct (sigma f) => //.
  asimpl.
  rewrite/scons/funcomp. 
  destruct j => //.
  destruct f => //.
  destruct (sigma f) => //.
Qed. 

Lemma injectiveS_InSP {n m : nat} : forall x (P : proc n.+1) (sigma: fin n -> ch m),
    injectiveS (InSP x P) sigma -> injectiveS P (up_ch_ch sigma).
Proof. 
  move => x P sigma.
  rewrite/injectiveS => H i j H1 H2.
  destruct i.
  destruct j.
  asimpl => Hyp.
  f_equal; f_equal.
  apply/H => //=.
  by right.
  by right.
  move:Hyp.
  rewrite/funcomp.
  destruct (sigma f) => //.
  destruct (sigma f0) => //=.
  by case => ->. 
  asimpl.
  rewrite/funcomp.
  destruct (sigma f) => //.
  asimpl.
  rewrite/scons/funcomp. 
  destruct j => //.
  destruct (sigma f) => //.
Qed.

Lemma injectiveS_DelP {n m : nat} : forall x y (P : proc n) (sigma: fin n -> ch m),
    injectiveS (DelP x y P) sigma -> injectiveS P sigma.
Proof. 
  move => x y P sigma.
  rewrite/injectiveS => H i j H1 H2 H3.
  apply/H => //=.
  by right;right.
  by right;right.
Qed.  

Lemma injectiveS_scons_shift {n : nat} : forall i (P : proc n.+1),
    ~(free_in (var_ch (shift i)) P) -> injectiveS P (scons (var_ch i) ids).
Proof.
  move => i P H. 
  rewrite/injectiveS => i0 j H1 H2 H3.
  have fact1 : shift i <> i0. 
  { rewrite/not.
    destruct i0 => //.
    move => Hyp.
    rewrite Hyp in H => //.
  }
  have fact2 : shift i <> j. 
  { rewrite/not.
    destruct j => //.
    move => Hyp.
    rewrite Hyp in H => //.
  }
  move:H3.
  rewrite/scons. 
  destruct i0 => //.
  destruct j => //.
  by case => ->.
  case; move => Hyp; subst => //.
  destruct j => //.
  case; move => Hyp; subst => //.
Qed.

Lemma injectiveS_swap {n : nat} : forall j k (P : proc n), injectiveS P (swap_ch j k).
Proof.
  move => j k P.
  rewrite/injectiveS => i j0 _ _.
  rewrite/swap_ch; case. 
  case: ifP. 
  - (* i == j *)
    move/eqP ->.
    case: ifP. 
    + (* i' == j *)
      move/eqP -> => //.
    + (* i' != j *)
      move/eqP => Hyp.
      case: ifP. 
      * (* i' == k *)
        move/eqP -> => //.
      * (* i' != k *)
        move/eqP => Hyp'.
        move => Hyp''; subst => //.
  - (* i != j *)
    move/eqP => Hyp.
    case: ifP.
    + (* i == k *)
      move/eqP ->.
      case: ifP.
      * move/eqP -> => //. 
      * move/eqP => Hyp'.
        case: ifP. 
        move/eqP -> => //.
        move/eqP => Hyp'' => H; subst => //.
    + (* i != k *)
      move/eqP => Hyp'.
      case: ifP. 
      * move/eqP => _ H; subst => //.
      * move/eqP => Hyp''.
        case: ifP.
        move/eqP -> => //.
        move/eqP => _ //.
Qed.         

(* End of injectiveS *)




(* InjectiveNS -- injective on i wrt a given set (as free names) *) 
Definition injectiveNS {n : nat} {m : nat} (i : fin n) (P: proc n) := 
  fun (f : fin n -> ch m) =>
    forall j: fin n, free_in (var_ch j) P -> (f i) = (f j) -> i = j.

Lemma injectiveNS_up_ch_ch_ResP {n : nat} {m : nat} : forall i P sigma,
    injectiveNS i (ResP P) sigma -> 
    injectiveNS (shift (shift i)) P (up_ch_ch (@up_ch_ch n m sigma)).
Proof.
  move => i P sigma Hinj j H1 H2. 
  destruct j.
  rewrite/shift. 
  f_equal.
  destruct f. 
  f_equal.
  apply/Hinj => //.
  move:H2. 
  asimpl.
  rewrite/funcomp/shift/subst_ch => /=.
  case (sigma f).
  case (sigma i) => f0 f1.
  case => H.
  by subst. 
  move:H2. 
  asimpl.
  rewrite/funcomp/shift/subst_ch => /=.
  destruct (sigma i) => f0 => //.
  move:H2. 
  asimpl.
  rewrite/funcomp/shift/subst_ch => /=.
  destruct (sigma i) => f0 => //.
Qed. 

Lemma injectiveNS_up_ch_ch_ParPL {n : nat} {m : nat} : forall i P Q sigma,
    injectiveNS i (ParP P Q) sigma -> @injectiveNS n m i P sigma.
Proof.
  move => i P Q sigma Hinj.
  rewrite/injectiveNS => j1 H1 H2.
  apply/Hinj => //=.
  by left.
Qed. 

Lemma injectiveNS_up_ch_ch_ParPR {n : nat} {m : nat} : forall i P Q sigma,
    injectiveNS i (ParP P Q) sigma -> @injectiveNS n m i Q sigma.
Proof.
  move => i P Q sigma Hinj.
  rewrite/injectiveNS => j1 H1 H2.
  apply/Hinj => //=.
  by right.
Qed. 

Lemma injectiveNS_up_ch_ch_InSP {n : nat} {m : nat} : forall i x P sigma,
    injectiveNS i (InSP x P) sigma -> injectiveNS (shift i) P (@up_ch_ch n m sigma).
Proof.
  move => i x P sigma Hinj j H1 H2. 
  destruct j.
  rewrite/shift. 
  f_equal.
  apply/Hinj => //.
  move:H1 => /= => H1. 
  by right. 
  move:H2. 
  asimpl.
  rewrite/funcomp/shift/subst_ch => /=.
  destruct (sigma i) => H2 => //.
  destruct (sigma f) => //.
  f_equal.
  move:H2.
  by case.
  move:H2.
  asimpl.
  rewrite/funcomp/shift/subst_ch => /=.
  by destruct (sigma i).
Qed. 

Lemma injectiveNS_up_ch_ch_DelSP {n : nat} {m : nat} : forall i x y P sigma,
    injectiveNS i (DelP x y P) sigma -> @injectiveNS n m i P sigma.
Proof.
  move => i [j] [j0] P sigma Hinj.
  rewrite/injectiveNS => j1 H1 H2.
  apply/Hinj => //=.
  by right; right. 
Qed. 


Lemma injectiveNS_up_ch_ch_zero1 {n : nat} {m : nat}: 
  forall (P : proc n.+1) (sigma : fin n -> ch m),
    injectiveNS var_zero P (up_ch_ch sigma).
Proof.
  move => P sigma; asimpl.
  rewrite/injectiveNS/var_zero/funcomp/shift/subst_ch/scons => x Hyp /=. 
  destruct x => //; destruct (sigma f) => //.
Qed. 

Lemma injectiveNS_up_ch_ch_zero2 {n : nat} {m : nat}: 
  forall (P : proc n.+2) (sigma : fin n -> ch m),
    injectiveNS var_zero P (up_ch_ch (up_ch_ch sigma)).
Proof.
  move => P sigma; asimpl.
  rewrite/injectiveNS/var_zero/funcomp/shift/subst_ch/scons => x Hyp /=. 
  destruct x => //; destruct f => //; destruct (sigma f) => //.
Qed. 


Lemma injectiveNS_up_ch_ch_one {n : nat} {m : nat}: 
  forall (P : proc n.+2) (sigma : fin n -> ch m),
    injectiveNS var_one P (up_ch_ch (up_ch_ch sigma)).
Proof.
  move => P sigma; asimpl.
  rewrite/injectiveNS/var_zero/funcomp/shift/subst_ch/scons => x Hyp /=. 
  destruct x => //; destruct f => //; destruct (sigma f) => //.
Qed. 

Lemma injectiveNS_shift_shift {n : nat} : forall i P,
    injectiveNS i P (fun j : fin n => var_ch (shift (shift j))).
  by move => i P; rewrite/injectiveNS => j H; case. 
Qed. 


Lemma injectiveNS_swap {n : nat} : forall i j k (P : proc n),
    injectiveNS i P (swap_ch j k).
Proof.
  rewrite/injectiveNS => i j k _ i' _.
  rewrite/swap_ch; case. 
  case: ifP. 
  - (* i == j *)
    move/eqP ->.
    case: ifP. 
    + (* i' == j *)
      move/eqP -> => //.
    + (* i' != j *)
      move/eqP => Hyp.
      case: ifP. 
      * (* i' == k *)
        move/eqP -> => //.
      * (* i' != k *)
        move/eqP => Hyp'.
        move => Hyp''; subst => //.
  - (* i != j *)
    move/eqP => Hyp.
    case: ifP.
    + (* i == k *)
      move/eqP ->.
      case: ifP.
      * move/eqP -> => //. 
      * move/eqP => Hyp'.
        case: ifP. 
        move/eqP -> => //.
        move/eqP => Hyp'' => H; subst => //.
    + (* i != k *)
      move/eqP => Hyp'.
      case: ifP. 
      * move/eqP => _ H; subst => //.
      * move/eqP => Hyp''.
        case: ifP.
        move/eqP -> => //.
        move/eqP => _ //.
Qed.         


Lemma injectiveNS_scons_shift {n : nat} : forall i j P,
    ~((shift (shift i)) = j) -> 
      injectiveNS (shift (shift (@shift n i))) P (scons (var_ch j) ids).
Proof.
  move => i j P H. 
  rewrite/injectiveNS => x _.
  case: x => H'; asimpl.
  by case => <-.
  move: H.
  move: H'. 
  asimpl.
  case => <-. 
  by case. 
Qed.

Lemma free_in_subst_aux {n : nat} {m : nat} : 
  forall x (sigma : fin n -> ch m) (P : proc n),
    free_in x (subst_proc sigma P) -> 
    exists i, free_in (var_ch i) P /\ sigma i = x.
Proof. 
  move => [j] sigma P; elim: P m sigma j => //.
  - move => n0 [i] P IH m sigma j H => //. 
    move: H => /=; case.
    + move => <-.
      exists i. 
      split => //. 
      by left. 
    + move/IH.
      case => x [H1 H2].
      exists x.
      split => //.
      by right. 
  - move => n0 [i] P IH m sigma j H => //. 
    move: H => /=; case.
    + move => <-.
      exists i. 
      split => //. 
      by left. 
    + move/IH.
      case => x [H1 H2].
      exists x.
      split => //.
      by right. 
  - move => n0 P IH m sigma j => /=.
    move/IH.
    case => x [H1 H2].
    destruct x => //.
    destruct f => //.
    exists f. 
    split => //.
    move: H2 => /=. 
    rewrite/funcomp/shift/up_ch_ch/subst_ch/funcomp => /=.
    destruct (sigma f).
    by case => ->.
  - move => n0 P IH1 Q IH2 m sigma j => /=.
    case. 
    * move/IH1. 
      case => x0 [H1 H2].
      exists x0.
      split => //.
      by left. 
    * move/IH2. 
      case => x0 [H1 H2].
      exists x0.
      split => //.
      by right. 
  - move => n0 [i] P IH m sigma j => /=.
    case. 
    * move => H. 
      exists i. 
      split => //.
      by left. 
    * move/IH.
      case => i1 [H1 H2].
      destruct i1 => //. 
      exists f. 
      split.
      by right. 
      move: H2.
      asimpl.
      rewrite/funcomp/shift => /=.
      destruct (sigma f).
      by case => ->.
  - move => n0 [i] [i0] P IH m sigma j => /=.
    case. 
    * move => H. 
      exists i. 
      split => //.
      by left. 
    * case.
      + move => H. 
        exists i0. 
        split => //.
        by right; left. 
    * move/IH.
      case => i1 [H1 H2].
      exists i1.
      split => //. 
      by right; right. 
Qed. 


Lemma free_in_subst {n : nat} {m : nat} : 
  forall (i : fin n) (sigma : fin n -> ch m) (P : proc n),
    free_in (subst_ch sigma (var_ch i)) (subst_proc sigma P) 
    -> injectiveNS i P sigma 
    -> free_in (var_ch i) P.
Proof. 
  move => i sigma P. 
  move/free_in_subst_aux.
  case => j. 
  case => H1 H2 H3. 
  have fact : i = j. 
  apply/H3 => //. 
  by subst. 
Qed.

Lemma free_in_subst_inv {n : nat} {m : nat} : 
  forall (i : fin n) (sigma : fin n -> ch m) (P : proc n),
    free_in (var_ch i) P
    -> free_in (subst_ch sigma (var_ch i)) (subst_proc sigma P).
Proof. 
  move => i sigma P; elim: P m i sigma => //=.
  - move => n0 [j] P IH m i sigma.
    asimpl.
    case. 
    * case => ->. 
      by left. 
    * move => H; right.
      by apply/IH.
  - move => n0 [j] P IH m i sigma.
    asimpl.
    case. 
    * case => ->. 
      by left. 
    * move => H; right.
      by apply/IH.
  - move => n0 P IH m i sigma. (* Restriction case *)
    move/(IH _ (shift (shift i)) (up_ch_ch (up_ch_ch sigma))).
    have fact : (up_ch_ch (up_ch_ch sigma) (shift (shift i))) =
                  (subst_ch (fun i0 : fin m => var_ch (shift (shift i0))) (sigma i))
      by asimpl. 
    by rewrite fact. 
  - move => n0 P IH1 Q IH2 m i sigma. 
    case. 
    * move => H.
      left.
      apply/(IH1 _ _ sigma) => //.
    * move => H.
      right.
      apply/(IH2 _ _ sigma) => //.
  - move => n0 [j] P IH m i sigma => /=.    
    case. 
    * case => ->.
      by left. 
    * move => H; right.
      move: H => /(IH _ _ (up_ch_ch sigma)).
      have fact : (up_ch_ch sigma (shift i)) = 
                    (subst_ch (fun i0 : fin m => var_ch (shift i0)) (sigma i))
        by asimpl.
    by rewrite fact. 
  - move => n0 [j] [j0] P IH m i sigma => /=.    
    case. 
    * by case => ->; left. 
    * case.
      + by case => ->; right; left. 
      + move => H; right; right.
        apply (IH _ _ sigma) => //.
Qed.  

Lemma free_in_congruence {n : nat} : forall (x : ch n) (P Q : proc n),
    struct_eq P Q -> free_in x Q <-> free_in x P.
Proof.
  move => x P Q Hred; elim: Hred x => //=.
  - by move => n0 P0 Q0 x; rewrite or_comm. 
  - by move => n0 P0 Q0 R x; rewrite or_assoc. 
  - split. 
    by move => H; left. 
    case => //.
  - move => n0 P0 Q0 [i].
    split. 
    + case. 
      * by move => H; left. 
      * move => H; right. 
        apply (free_in_subst i (fun i : fin n0 => var_ch (shift (shift i)))) => //.
        apply/injectiveNS_shift_shift.
    + case. 
      * by left.
      * by right; apply/free_in_subst_inv. 
  - move => n0 P0 [i]. 
    split => /=.
    + move => H. 
      apply/(free_in_subst _ (swap_ch var_zero var_one)).
      have fact : subst_ch (swap_ch var_zero var_one) (var_ch (shift (shift i))) =
                    (var_ch (shift (shift i))) by asimpl.
      by rewrite fact. 
      apply/injectiveNS_swap.
    + move/free_in_subst_inv.
      apply.
  - move => n0 P0 [i] => /=.
    split. 
    + move => H.
      apply/(free_in_subst _ (swap_ch var_zero var_two)).
      apply/(free_in_subst _ (swap_ch var_one var_three)) => //.
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
    + move/(free_in_subst_inv _ (swap_ch var_zero var_two)).
      by move/(free_in_subst_inv _ (swap_ch var_one var_three)).
  - by move => n0 P0 Q0 Heq H x; apply iff_sym.
  - by move => n0 P0 Q0 R Heq1 H Heq2 H' x; rewrite -H.
  - by move => n0 P0 P' Q0 Q' Heq1 H1 Heq2 H2 x; rewrite -H1 -H2.
  - by move => n0 P0 P' x Heq H x0; rewrite -H.
  - by move => n0 P0 P' x Heq H x0; rewrite -H.
  - by move => n0 P0 P' x y Heq H x0; rewrite -H.
  - by move => n0 P0 P' x Heq H x0; rewrite -H.
Qed. 


Lemma free_in_reduction {n : nat} : forall (x : ch n) (P Q : proc n),
    reduce P Q -> free_in x Q -> free_in x P.
Proof.
  move => [i] P Q Hred; elim: Hred i.
  - by move => n0 P0 Q0 Hred IH i =>/= => H; apply/IH.
  - move => n0 P0 Q0 R Hred IH i =>/= => Hyp.
    inversion Hyp.
    left.
    by apply/IH.
    by right. 
  - move => n0 P0 P' Q0 Q' Hstruct1 Hred1 IH Hstruct2 i H. 
    apply/(free_in_congruence _ _ P') => //. 
    apply/IH.
    apply/(free_in_congruence _ _ Q0) => //. 
  - move => n0 P0 Q0 i /=.
    case. 
    by move => H; left; right. 
    by move => H; right; right. 
  - move => n0 [j] P0 Q0 i /=.
    case. 
    * by move => H; left; right; right.
    * move => H. 
      case: (fin_eq_dec (shift (shift i)) j). 
      + by move => ->; left; right; left.
      + move => H1; right; right.
        apply/free_in_subst.
        apply/H.
        by apply/injectiveNS_scons_shift. 
Qed.


(* Some extra lemmas *)

Lemma free_in_0_shift {n : nat} : forall (P : proc n),
    ~free_in (var_ch var_zero) (shift_two_up P).
Proof.
  move => P.
  rewrite/not/shift_two_up.
  move/(free_in_subst_aux).
  case => x0 [H1 H2].
  inversion H2.
Qed.

Lemma free_in_1_shift {n : nat} : forall (P : proc n),
    ~free_in (var_ch var_one) (shift_two_up P).
Proof.
  move => P.
  rewrite/not/shift_two_up.
  move/(free_in_subst_aux).
  case => x0 [H1 H2].
  inversion H2.
Qed.

(* <<<<<<< HEAD *)
(* ======= *)
(* Lemma free_ch_subst_exists {n : nat} {m : nat} :  *)
(*   forall x (sigma : fin n -> ch m) (P : proc n), *)
(*     free_in x (subst_proc sigma P) ->  *)
(*     exists i, free_in (var_ch i) P /\ sigma i = x. *)
(* Admitted. *)
(* >>>>>>> 83ad6a04e18af8256cf62c271bdbaf409fdd0f6b *)
(* Lemma free_ch_0_shift {n : nat} : forall (P : proc n),  *)
(*     ~free_in (var_ch var_zero) (shift_two_up P).  *)
(* Proof. *)
(*   move => P. *)
(* <<<<<<< HEAD *)
(*   rewrite/not/shift_two_up.  *)
(*   move/(free_in_subst_aux). *)
(*   case => x0 [H1 H2]. *)
(*   inversion H2.  *)
(* Qed.    *)

(* ======= *)
(*   rewrite/not/shift_up.  *)
(*   Admitted. *)
(*   (* *)
(*   move/(free_in_subst).  *)
(*   asimpl. *)
(*   rewrite/funcomp/shift. => H. *)


(*   move/free_ch_subst_domain_codomain. *)
(*   case => x.  *)
(*   case => _ /=. *)
(*   move => H. *)
(*   inversion H.  *)
(* Qed.    *)
(* *) *)
(* Lemma free_in_subst' {n : nat} {m : nat} :  *)
(*   forall (i : fin n) (sigma : fin n -> ch m) (P : proc n), *)
(*     free_in (subst_ch sigma (var_ch i)) (subst_proc sigma P)  *)
(*     -> injectiveNS i P sigma  *)
(*     -> free_in (var_ch i) P. *)
(* Admitted. *)
(* >>>>>>> 83ad6a04e18af8256cf62c271bdbaf409fdd0f6b *)

(* Lemma free_ch_1_shift {n : nat} : forall (P : proc n),  *)
(*     ~free_in (var_ch var_one) (shift_two_up P).  *)
(* Proof. *)
(*   move => P. *)
(*   rewrite/not/shift_two_up.  *)
(*   move/(free_in_subst_aux). *)
(*   case => x0 [H1 H2]. *)
(*   inversion H2.  *)
(* Qed.    *)

(* Lemma injectiveNS_swap_zero_one {n : nat} : forall (i : fin n) (P : proc n.+2), *)
(*     injectiveNS (shift (shift i)) P (swap_ch var_zero var_one). *)
(* Proof.  *)
(*   move => i P; rewrite/injectiveNS => j H1 H2.  *)
(*   destruct j. *)
(*   destruct f.  *)
(*   inversion H2 => //. *)
(*   inversion H2. *)
(*   inversion H2.  *)
(* Qed.  *)

(* Lemma injectiveNS_swap_one_three {n : nat} : forall (i : fin n) (P : proc n.+4), *)
(*     injectiveNS (shift (shift (shift (shift i)))) *)
(*       P (swap_ch var_one var_three). *)
(* Proof.  *)
(*   move => i P; rewrite/injectiveNS => j H1 H2.  *)
(*   destruct j. *)
(*   repeat destruct f.  *)
(*   inversion H2 => //. *)
(*   inversion H2. *)
(*   inversion H2.  *)
(*   inversion H2. *)
(*   inversion H2.  *)
(* Qed.  *)

(* Lemma injectiveNS_swap_zero_two {n : nat} : forall (i : fin n) (P : proc n.+4), *)
(*     injectiveNS (shift (shift (shift (shift i)))) *)
(*       P (swap_ch var_zero var_two). *)
(* Proof.  *)
(*   move => i P; rewrite/injectiveNS => j H1 H2.  *)
(*   destruct j. *)
(*   repeat destruct f.  *)
(*   inversion H2 => //. *)
(*   inversion H2. *)
(*   inversion H2.  *)
(*   inversion H2. *)
(*   inversion H2.  *)
(* Qed.  *)
