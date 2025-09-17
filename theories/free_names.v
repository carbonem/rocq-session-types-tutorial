(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import synsem. 
Open Scope subst_scope.

(** Note: remaining asimpl are needed*)
Fixpoint free_in {n : nat} (z : ch n) (P : proc n ) := 
  match P with
  | EndP       => False
  | WaitP x P  => (x = z) \/ (free_in z P)
  | CloseP x P => (x = z) \/ (free_in z P)
  | ResP P     => free_in ((shift \o shift ) z) P
  | ParP P Q   => (free_in z P) \/ (free_in z Q)
  | InSP x P   => (x = z) \/ 
                    (free_in (shift  z) P)
  | DelP x y P => (x = z) \/ (y = z) \/ free_in z P
end.

Definition injectiveS {n : nat} {m : nat} (P: proc n) := 
  fun (f : ch n -> ch m) =>
    forall x y: ch n, free_in x P -> free_in y P ->
                      (f x) = (f y) -> x = y.

Lemma injectiveS_ResP {n m : nat} :
  forall (P : proc n.+2) (sigma : ren n m),
    injectiveS (ResP P) sigma ->
    injectiveS P (up_ch (up_ch sigma)). 
Proof. 
  move => P sigma.
  rewrite/injectiveS/up_ch => H x y H1 H2.
  destruct x => /=.
  destruct y => //=. 
  destruct c => /=.
  destruct c0 => //=.
  case => Hyp.
  repeat f_equal. 
  apply/H => //.
  destruct c0 => //.
  destruct y => //.
Qed. 

Lemma injectiveS_InSP {n m : nat} :
  forall x (P : proc n.+1) (sigma: ch n -> ch m),
    injectiveS (InSP x P) sigma ->
    injectiveS P (up_ch sigma).
Proof. 
  move => x P sigma.
  rewrite/injectiveS/up_ch => H x0 y H1 H2.
  destruct x0 => //.
  destruct y => //.
  case => Hyp.
  f_equal.
  apply/H => //=.
  by right.
  by right.
  destruct y => //.
Qed. 

Lemma injectiveS_DelP {n m : nat} :
  forall x y (P : proc n) (sigma: ch n -> ch m),
    injectiveS (DelP x y P) sigma -> injectiveS P sigma.
Proof. 
  move => x y P sigma.
  rewrite/injectiveS => H i j H1 H2 H3.
  apply/H => //=.
  by right;right.
  by right;right.
Qed.  

Lemma injectiveS_scons_shift {n : nat} :
  forall (x : ch n) (P : proc n.+1),
    ~(free_in (shift x) P) ->
    injectiveS P (scons x id_ren).
Proof.
  move => x P H. 
  rewrite/injectiveS/scons => x0 y H1 H2.
  destruct x0 => //.
  destruct y => //.
  by rewrite/id_ren => ->.
  have fact : x <> c 
    by rewrite/not; move: H => /[swap] => -> //.
  by rewrite/id_ren => Hyp; subst.
  destruct y => //.
  have fact : x <> c 
    by rewrite/not; move: H => /[swap] => -> //.
  by rewrite/id_ren => Hyp; subst.
Qed.

Lemma injectiveS_swap {n : nat} : forall x y (P : proc n),
    injectiveS P (swap_ch x y).
Proof.
  move => j k P.
  rewrite/injectiveS => i j0 _ _.
  rewrite/swap_ch. 
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




(* InjectiveNS -- injective on x wrt a given set (as free names) *) 
Definition injectiveNS {n m : nat} (x : ch n) (P: proc n) := 
  fun (sigma : ren n m) =>
    forall y: ch n, free_in y P -> sigma x = sigma y -> x = y.

Lemma injectiveNS_ResP {n m : nat} :
  forall (x : ch n) (P : proc n.+2) (sigma : ren n m),
    injectiveNS x (ResP P) sigma -> 
    injectiveNS (shift (shift x)) P (up_ch (up_ch sigma)).
Proof.
  move => x P sigma Hinj y H1 H2. 
  destruct y => //.
  destruct c => //.
  rewrite/shift. 
  repeat f_equal.
  apply/Hinj => //.
  move:H2 => /=.
  by case. 
Qed. 

Lemma injectiveNS_ParPL {n : nat} {m : nat} :
  forall (x : ch n) (P Q : proc n) (sigma : ren n m),
    injectiveNS x (ParP P Q) sigma -> injectiveNS x P sigma.
Proof.
  move => x P Q sigma Hinj j1 H1 H2.
  apply/Hinj => //=.
  by left.
Qed. 

Lemma injectiveNS_ParPR {n : nat} {m : nat} :
  forall (x : ch n) (P Q : proc n) (sigma : ren n m),
    injectiveNS x (ParP P Q) sigma -> injectiveNS x Q sigma.
Proof.
  move => x P Q sigma Hinj j1 H1 H2.
  apply/Hinj => //=.
  by right.
Qed. 

Lemma injectiveNS_InSP {n : nat} {m : nat} :
  forall (x y : ch n)  (P : proc n.+1) (sigma : ren n m),
    injectiveNS x (InSP y P) sigma ->
    injectiveNS (shift x) P (up_ch sigma).
Proof.
  move => x y P sigma Hinj z H1 H2. 
  destruct z => //.
  rewrite/shift. 
  f_equal.
  apply/Hinj.
  move: H1 => /= => H1. 
  by right. 
  move:H2 => /=. 
  by case. 
Qed. 

Lemma injectiveNS_DelSP {n : nat} {m : nat} :
  forall (x y z : ch n) (P : proc n) (sigma : ren n m),
    injectiveNS x (DelP y z P) sigma -> injectiveNS x P sigma.
Proof.
  move => x y z P sigma Hinj x' H1 H2.
  apply/Hinj => //=.
  by right; right. 
Qed. 


Lemma injectiveNS_up_ch_zero1 {n : nat} {m : nat}: 
  forall (P : proc n.+1) (sigma : ren n m),
    injectiveNS zero P (up_ch sigma).
Proof.
  move => P sigma x Hyp /=. 
  destruct x => //; destruct (sigma f) => //.
Qed. 

Lemma injectiveNS_up_ch_zero2 {n : nat} {m : nat}: 
  forall (P : proc n.+2) (sigma : ren n m),
    injectiveNS zero P (up_ch (up_ch sigma)).
Proof.
  move => P sigma x Hyp /=. 
  destruct x => //; destruct f => //; destruct (sigma f) => //.
Qed. 


Lemma injectiveNS_up_ch_one {n : nat} {m : nat}: 
  forall (P : proc n.+2) (sigma : ren n m),
    injectiveNS one P (up_ch (up_ch sigma)).
Proof.
  move => P sigma x Hyp /=. 
  destruct x => //; destruct c => //; destruct (sigma c) => //.
Qed. 

Lemma injectiveNS_shift_shift {n : nat} : forall x P,
    injectiveNS x P (fun y : ch n => shift (shift y)).
  by move => y P; rewrite/injectiveNS => z H; case. 
Qed. 



Lemma injectiveNS_swap {n : nat} : forall x y z (P : proc n),
    injectiveNS x P (swap_ch y z).
Proof.
  move => x y z _ x' _.
  rewrite/swap_ch. 
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
      injectiveNS (shift (shift (@shift n i))) P (scons j id_ren).
Proof.
  move => i j P H x _ /=.
  rewrite/id_ren.
  destruct x => //=. 
  by move => <-.
Qed.


(* substitution lemmas *) 
Lemma free_in_subst {n : nat} {m : nat} : 
  forall (x : ch n) (sigma : ren n m) (P : proc n),
    free_in x P -> free_in (sigma x)  ((< sigma >) P).
Proof. 
  move => x sigma P; elim: P m x sigma => //=.
  - move => n0 c P IH m x sigma.
    case. 
    * move => ->; left => //.
    * move => H; right.
      by apply/IH.
  - move => n0 c P IH m x sigma.
    case. 
    * move => ->; left => //.
    * move => H; right.
      by apply/IH.
  - move => n0 P IH m x sigma. (* Restriction case *)
    move/(IH _ (shift (shift x)) (up_ch (up_ch sigma))) => //.
  - move => n0 P IH1 Q IH2 m x sigma.
    case. 
    * move => H; left.
      apply/(IH1 _ _ sigma) => //.
    * move => H; right.
      apply/(IH2 _ _ sigma) => //.
  - move => n0 c P IH m x sigma.
    case. 
    * by move => ->; left.
    * move => H; right.
      move: H => /(IH _ _ (up_ch sigma)) => //.
  - move => n0 c c0 P IH m x sigma => /=.    
    case. 
    * by move => ->; left. 
    * case.
      + by move => ->; right; left. 
      + move => H; right; right.
        apply (IH _ _ sigma) => //.
Qed.  

Lemma free_in_subst_inv_aux {n : nat} {m : nat} : 
  forall x (sigma : ren n m) (P : proc n),
    free_in x (subst_proc sigma P) -> 
    exists y, free_in y P /\ sigma y = x.
Proof. 
  move => x sigma P; elim: P m sigma x => //.
  - move => n0 x P IH m sigma y H => //. 
    move: H => /=; case.
    + eauto.  
    + move/IH.
      case => y0 [H1 H2].
      firstorder.
      - move => n0 x P IH m sigma y H => //. 
    move: H => /=; case.
    + move => <-. eauto.
       
    + move/IH.
      case => y0 [H1 H2].
      eauto. 
  - move => n0 P IH m sigma y => /=.
    move/IH.
    case => x [H1 H2].
    move: H2.
    destruct x => //.
    destruct c => //=.
    case => <-. 
    exists c => //.
  - move => n0 P IH1 Q IH2 m sigma y => /=.
    case. 
    * move/IH1. 
      case => x0 [H1 H2].
      eauto. 
    * move/IH2. 
      case => x0 [H1 H2].
      eauto.
     - move => n0 x P IH m sigma y => /=.
    case. 
    * eauto. 
    * move/IH.
      case => x1 [H1 H2].
      destruct x1 => //.
      exists c.
 
      split.
      by right. 
      move: H2 => /=.
      by case. 
  - move => n0 x x0 P IH m sigma y => /=.
    case. 
    * eauto.  
    * case.
      + eauto.  
    * move/IH.
      case => x1 [H1 H2].
      eauto. 
Qed. 

Lemma free_in_subst_inv {n : nat} {m : nat} : 
  forall (x : ch n) (sigma : ren n m) (P : proc n),
    free_in (sigma x) (subst_proc sigma P) 
    -> injectiveNS x P sigma 
    -> free_in x P.
Proof. 
  move => x sigma P. 
  move/free_in_subst_inv_aux.
  case => y. 
  case => H1 H2 H3. 
  have fact : x = y by  apply/H3 => //. 
  by subst. 
Qed.


(* Congruence result *) 
Lemma free_in_congruence {n : nat} :
  forall (x : ch n) (P Q : proc n),
    P ≅ Q  -> free_in x Q <-> free_in x P.
Proof.
  move => x P Q Hred; elim: Hred x => //=.
  all: firstorder. 
  - right.
    apply (free_in_subst_inv x
             (fun i : ch n0 => (shift (shift i)))) => //.
    apply/injectiveNS_shift_shift.
  - right. 
    by apply/(free_in_subst x (fun x0 : ch n0 => shift (shift x0))).
  - apply/(free_in_subst_inv _ (swap_ch zero one)) => //.
    apply/injectiveNS_swap.
  - move: H.
    move/free_in_subst.
    apply.
  - apply/(free_in_subst_inv _ (swap_ch zero two)).
    apply/(free_in_subst_inv _ (swap_ch one three)) => //.
    apply/injectiveNS_swap.
    apply/injectiveNS_swap.
  - move: H.
    move/(free_in_subst _ (swap_ch zero two)).
    by move/(free_in_subst _ (swap_ch one three)).
Qed. 


Lemma free_in_reduction {n : nat} : forall (x : ch n) (P Q : proc n),
    P ⇛ Q  -> free_in x Q -> free_in x P.
Proof.
  move => x P Q Hred; elim: Hred x => /=.
  all: firstorder. 
  - apply/(free_in_congruence _ _ P') => //. 
    apply/H1.
    apply/(free_in_congruence _ _ Q0) => //. 
  - case Hyp: ((Some (Some x0)) == x).
    move: Hyp H => /eqP => <-; firstorder. 
    right; right.
    apply/free_in_subst_inv.
    apply/H.
    apply/injectiveNS_scons_shift. 
    move: Hyp => /eqP => //.
Qed.


(* Some extra lemmas *)

Lemma free_in_bounded_shift {n : nat} : forall (P : proc n) x,
    (forall y : ch n, shift (shift y) <> x) ->
    ~free_in x (subst_proc (shift \o shift) P).
Proof.
  move => P x H.
  rewrite/not.
  move/(free_in_subst_inv_aux).
  case => y [H1 H2].
  have : shift (shift y) <> x by apply H.
  contradiction.
Qed.

Corollary free_in_0_shift {n : nat} (P : proc n):
    ~free_in zero (subst_proc (shift \o shift) P).
Proof.
  apply free_in_bounded_shift; intros y cc; inversion cc.
  Qed.
  

Corollary free_in_1_shift {n : nat} (P : proc n):
    ~free_in one (subst_proc (shift \o shift) P).
Proof.
  apply free_in_bounded_shift; intros y cc; inversion cc.
  Qed.  