(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import core fintype free_names syntax semantics. 

(* Linear Predicate *)
Inductive lin {n : nat} : (ch n) -> proc n -> Prop :=
| LWaitP x P          : not (free_in x P) ->
                        lin x (WaitP x P)
| LWaitPcongr x y P   : lin y P ->
                        not(x = y) -> 
                        lin y (WaitP x P)
| LCloseP x P         : not (free_in x P) ->
                        lin x (CloseP x P)
| LClosePcongr x y P  : lin y P -> 
                        not (x = y) -> 
                        lin y (CloseP x P)
| LResP  x P          : lin (subst_ch (fun i => var_ch (shift (shift i))) x)
                          P ->
                        lin x (ResP P)
| LParPL x P1 P2      : lin x P1 -> 
                        not (free_in x P2) ->
                        lin x (ParP P1 P2)
| LParPR x P1 P2      : not (free_in x P1) ->
                        lin x P2 ->
                        lin x (ParP P1 P2)
| LInSP x y P         : lin (var_ch var_zero) P -> 
                        lin (subst_ch (fun i => var_ch (shift i)) y) P ->
                        lin y (InSP x P)
| LDelP x y z P       : not (z=y) ->
                        lin z P -> 
                        lin z (DelP x y P)
| LDelPObj x y P      : not (x=y) -> 
                        not (free_in y P) ->
                        lin y (DelP x y P).


Lemma lin_subst {n : nat} {m : nat} : 
  forall (i : fin n) y (P : proc n) (sigma : fin n -> ch m), 
    lin (var_ch i) P -> 
    injectiveNS i P sigma -> 
    y = sigma i -> (* this just makes it easier applyin IH *)
    lin y (subst_proc sigma P).
Proof. 
  move => i [j] P; elim: P m i j => /=.
  - by intros; inversion H.  
  (* WaitP *)
  - move => n0 [j0] P IH m i j sigma => /= H1 => H2 H3.
    inversion H1; subst.
    * rewrite H3 => {H3 j}. 
      apply/LWaitP.
      move:H4.
      apply/contra_not. 
      move/(free_in_subst _ sigma); apply. 
      by rewrite/injectiveNS => j' Hyp; apply/H2 => /=; right.
    * apply/LWaitPcongr.
      apply/(IH _ i j) => //.
      by rewrite/injectiveNS => j' Hyp; apply/H2 => /=; right.
      move: H6. 
      apply/contra_not => Hyp.
      f_equal.
      apply/Logic.eq_sym. 
      apply/H2 => //=. 
      by left.  
      by rewrite -H3.
  (* CloseP *)
  - move => n0 [j0] P IH m i j sigma => /= H1 => H2 H3.
    inversion H1; subst.
    * rewrite H3 => {H3 j}. 
      apply/LCloseP.
      move:H4.
      apply/contra_not. 
      move/(free_in_subst _ sigma); apply. 
      by rewrite/injectiveNS => j' Hyp; apply/H2 => /=; right.
    * apply/LClosePcongr.
      apply/(IH _ i j) => //.
      by rewrite/injectiveNS => j' Hyp; apply/H2 => /=; right.
      move: H6. 
      apply/contra_not => Hyp.
      f_equal.
      apply/Logic.eq_sym. 
      apply/H2 => //=. 
      by left.  
      by rewrite -H3.
  (* ResP *)
  - move => n0 P IH m i j sigma H1 H2 H3.
    inversion H1; subst.
    apply/LResP => /=. 
    apply/(IH _ (shift (shift i))) => //.
    by apply/injectiveNS_up_ch_ch_ResP.
    asimpl. 
    by rewrite/funcomp -H3. 
  (* ParP *)
  - move => n0 P IH1 Q IH2 m i j sigma H1 H2 H3.
    inversion H1; subst. 
    * apply/LParPL.
      apply/(IH1 _ i) => //. 
      by apply/(injectiveNS_up_ch_ch_ParPL _ _ Q).
      move:H6.
      apply/contra_not => Hyp.
      apply/(free_in_subst _ sigma).
      move:Hyp.
      by rewrite H3.
      by apply/(injectiveNS_up_ch_ch_ParPR _ P).
    * apply/LParPR.
      move:H5.
      apply/contra_not => Hyp.
      apply/(free_in_subst _ sigma).
      move:Hyp.
      by rewrite H3.
      by apply/(injectiveNS_up_ch_ch_ParPL _ _ Q).
      apply/(IH2 _ i) => //. 
      by apply/(injectiveNS_up_ch_ch_ParPR _ P).
  (* InSP *) 
  - move => n0 c P IH m i j sigma H1 H2 H3. 
    inversion H1; subst. 
    apply/LInSP.
    apply/(IH _ var_zero) => //.
    apply/injectiveNS_up_ch_ch_zero1.
    apply/(IH _ (shift i)) => //.
    by apply/(injectiveNS_up_ch_ch_InSP _ c). 
    asimpl; rewrite/funcomp. 
    by rewrite -H3.
  (* DelP *) 
  - move => n0 [c] [c0] P IH m i j sigma H1 H2 H3. 
    inversion H1; subst => /=. 
    * apply/LDelP => /=.
      rewrite H3. 
      move:H5.
      apply/contra_not => Hyp.
      f_equal.
      apply/H2 => //. 
      by right; left. 
      apply/(IH _ i) => //.
      by apply/(injectiveNS_up_ch_ch_DelSP _ (var_ch c) (var_ch c0)).
    * rewrite H3. 
      apply/LDelPObj.
      move:H5.
      apply/contra_not => Hyp.
      f_equal.
      apply/Logic.eq_sym. 
      by apply/H2 => //=; left.
      move:H7.
      apply/contra_not.
      move/free_in_subst. 
      apply.
      by apply/(injectiveNS_up_ch_ch_DelSP _ (var_ch c) (var_ch c0)).
Qed.


Lemma lin_key_subst {n : nat} : forall (j : fin n.+2) (P : proc n.+3), 
    lin (var_ch var_zero) P -> 
    ~( free_in (var_ch (shift j)) P) -> 
    lin (var_ch j) (subst_proc (scons (var_ch j) ids) P).
Proof. 
  intros. 
  apply/(lin_subst _ _ _ _ H).
  rewrite/injectiveNS => j0 /=.
  intros. 
  case: (fin_eq_dec (shift j) j0). 
  intros; subst => //. 
  move: H2.
  rewrite/scons => /=.
  destruct j0 => //.
  case => ->.
  by case. 
  by asimpl.
Qed. 

Lemma lin_subst_inv {n : nat} {m : nat} : 
  forall (i : fin n) y (P : proc n) (sigma : fin n -> ch m), 
    lin y (subst_proc sigma P) ->
    injectiveNS i P sigma -> 
    y = sigma i -> (* this just makes it easier applyin IH *)
    lin (var_ch i) P.
Proof. 
  move => i [j] P sigma; elim: P m i j sigma => /=.
  - intros; inversion H.
  (* WaitP *)
  - move => n0 [j0] P IH m i j sigma /= H1 HInj H2.
    inversion H1; subst.
    * have fact: i = j0.
      apply/HInj.
      by left.
      by rewrite -H2.
      subst. 
      apply/LWaitP.
      move:H3.
      apply/contra_not.
      move/(free_in_subst_inv _ sigma).
      by rewrite H.
    * apply/LWaitPcongr => //.
      apply/(IH _ i j sigma) => //.
      rewrite/injectiveNS => j1 Hyp1 Hyp2.
      apply/HInj => //.
      by right. 
      move:H5.
      apply/contra_not.
      case => -> //.
  (* CLoseP *)
  - move => n0 [j0] P IH m i j sigma /= H1 HInj H2.
    inversion H1; subst.
    * have fact: i = j0.
      apply/HInj.
      by left.
      by rewrite -H2.
      subst. 
      apply/LCloseP.
      move:H3.
      apply/contra_not.
      move/(free_in_subst_inv _ sigma).
      by rewrite H.
    * apply/LClosePcongr => //.
      apply/(IH _ i j sigma) => //.
      rewrite/injectiveNS => j1 Hyp1 Hyp2.
      apply/HInj => //.
      by right. 
      move:H5.
      apply/contra_not.
      case => -> //.
  (* ResP *)
  - move => n0 P IH m i j sigma /= H1 HInj H2.
    inversion H1; subst. 
    apply/LResP. 
    apply/(IH _ (shift (shift i)) (shift (shift j)) 
             (up_ch_ch (up_ch_ch sigma))) => //=.
    by apply/injectiveNS_up_ch_ch_ResP.
    by asimpl; rewrite/funcomp -H2.
  (* ParP *)
  - move => n0 P IH1 Q IH2 m i j sigma /= H1 HInj H2.
    inversion H1; subst. 
    * apply/LParPL.
      apply/(IH1 _ i j sigma) => //. 
      by apply/(injectiveNS_up_ch_ch_ParPL _ _ Q).
      move:H5.
      apply/contra_not.
      move/(free_in_subst_inv _ sigma) => /=.
      by rewrite H2.
    * apply/LParPR.
      move:H4.
      apply/contra_not.
      move/(free_in_subst_inv _ sigma) => /=.
      by rewrite H2.
      apply/(IH2 _ i j sigma) => //. 
      by apply/(injectiveNS_up_ch_ch_ParPR _ P).
  (* InSP *)
  - move => n0 [k] P IH m i j sigma /= H1 HInj H2. 
    inversion H1; subst. 
    apply/LInSP => /=.
    apply/IH.
    apply/H4.
    apply/injectiveNS_up_ch_ch_zero1.
    by asimpl.
    apply/(IH _ _ (shift j) (up_ch_ch sigma)) => //=.
    by apply/(injectiveNS_up_ch_ch_InSP _ (var_ch k)).
    rewrite/funcomp/shift => /=.
    by rewrite -H2.
  (* DelP *)
  - move => n0 [k] [k0] P IH m i j sigma /= H1 HInj H2. 
    inversion H1; subst. 
    + apply/LDelP.
      move:H4. 
      apply/contra_not. 
      by case => <-.
      apply/(IH _ _ j sigma) => //.
      by apply/(injectiveNS_up_ch_ch_DelSP _ (var_ch k) (var_ch k0)).
    + (* need to prove that i = k0 *)
      have fact : i = k0.
      apply/HInj.
      by right;left.
      by rewrite -H0 H2.
      subst. 
      apply/LDelPObj.
      move:H4.
      apply/contra_not.
      by case => ->.
      move:H6.
      apply/contra_not => /(free_in_subst_inv _ sigma). 
      by rewrite H0.
Qed. 

   
Lemma lin_congruence {n : nat} : forall {x : ch n} P Q,
    struct_eq P Q -> lin x P <-> lin x Q.
Proof.
  move => [i] P Q H; elim: H i => //.
  - move => n0 P0 Q0.
    split.
    * move => H. 
      inversion H; subst. 
      by apply/LParPR.
      by apply/LParPL.
    * move => H. 
      inversion H; subst.
      by apply/LParPR. 
      by apply/LParPL. 
  - move => n0 P0 Q0 R0.
    split.
    * move => H.
      inversion H; subst. 
      + inversion H3; subst.
        apply/LParPL => //=.
        move:H6; apply/contra_not; case => //.
        apply/LParPR => //=.
        apply/LParPL => //=.
      + apply/LParPR.
        move: H3 => /=; apply/contra_not => Hyp. 
        by left. 
      + apply/LParPR => //. 
        move: H3 => /=; apply/contra_not => Hyp. 
        by right. 
    * move => H. 
      inversion H; subst. 
      + apply/LParPL.
        apply/LParPL => //=.
        move:H4; apply/contra_not => Hyp /=.
        by left. 
        move:H4; apply/contra_not => Hyp /=.
        by right. 
      + inversion H4; subst. 
        apply/LParPL. 
        apply/LParPR => //.
        by move: H3 => /=; apply/contra_not => Hyp. 
      + apply/LParPR => //=. 
        move: H3 => /=; apply/contra_not; case => //. 
  - move => m R i.
    split. 
    * move => H. 
      inversion H; subst  =>//=. 
      inversion H4.
    * move => H. 
      apply/LParPL => //.
  - move => m P0 Q0. (* extrusion case *)
    split. 
    { move => H. 
      inversion H => {H}; subst.
      + inversion H3; subst. 
        apply/LResP. 
        apply/LParPL =>//.
        move : H4. 
        apply/contra_not.
        asimpl.
        move/free_in_subst. 
        apply.
        rewrite/injectiveNS => x0 H.
        by case. 
      + apply/LResP.
        apply LParPR. 
        move : H3 => //=. 
        asimpl. 
        apply/(lin_subst) => //.
        apply/H4.
        rewrite/injectiveNS => n0 H. 
        by case. 
    }
    { move => H.
      inversion H => {H}; subst. 
      inversion H2 => {H2}; subst. 
      + apply/LParPL. 
        apply/LResP => //.
        move:H4 => /=.
        apply/contra_not => Hyp.
        apply/(free_in_subst_inv) => //=.
      + apply/LParPR => //=.
        apply/(lin_subst_inv _ (subst_ch
            (fun i => var_ch (shift (shift i))) (var_ch i))).
        apply/H4. 
        rewrite/injectiveNS => j _.
        by case.
        by asimpl.
    }
  - move => n0 R i. (* swapC *) 
    split. 
    {
      move => H. 
      inversion H;subst. 
      constructor => /=.
      apply/(lin_subst (shift (shift i)) _ _ (swap_ch var_zero var_one)) => //.
      apply/injectiveNS_swap.
    }
    {
      move => H.
      inversion H; subst. 
      constructor. 
      apply/lin_subst_inv.
      apply/H2. 
      apply/injectiveNS_swap.
      by asimpl.
    } 
  - move => R. (* swapB *)
    split.
    {
      move => H.
      inversion H;subst. 
      inversion H2;subst. 
      constructor; constructor => /=.
      apply/(lin_subst ) => //.
      apply/(lin_subst ) => //.
      apply/H3. 
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
      by asimpl.
    }
    {
      move => H. 
      inversion H; subst. 
      inversion H2; subst. 
      constructor. 
      constructor => /=. 
      apply/(lin_subst_inv). 
      apply/(lin_subst_inv (shift (shift (shift (shift i))))). 
      apply/H3. 
      apply/injectiveNS_swap.
      by asimpl.
      apply/injectiveNS_swap.
      by asimpl.
    }
  - move => n0 P0 Q0 H1 H2 i. 
    by apply iff_sym.
  - move => n0 P0 Q0 R Heq H1 Heq2 H2 i.
    by rewrite H1. 
  - move => n0 P0 P' Q0 Q' Heq1 H1 Heq2 H2 i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LParPL. 
      by rewrite -H1. 
      move: H5; apply/contra_not => Hyp'. 
      by apply/(free_in_congruence _ _ Q'). 
      apply/LParPR. 
      move: H4; apply/contra_not => Hyp'. 
      by apply/(free_in_congruence _ _ P'). 
      by rewrite -H2.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LParPL. 
      by rewrite H1. 
      move: H5; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ Q0) => //. 
      apply/LParPR. 
      move: H4; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //. 
      by rewrite H2.
  - move => n0 P0 P' Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LResP. 
      by rewrite -H. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LResP. 
      by rewrite H. 
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LCloseP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ _ P') => //.
      apply/LClosePcongr => //.
      by rewrite -H.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LCloseP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //.
      apply/LClosePcongr => //.
      by rewrite H.
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LWaitP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ _ P') => //.
      apply/LWaitPcongr => //.
      by rewrite -H.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LWaitP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //.
      apply/LWaitPcongr => //.
      by rewrite H.
  - move => n0 P0 P' x y Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LDelP => //. 
      by rewrite -H.
      apply/LDelPObj => //.
      move:H5; apply/contra_not => Hyp'.
      by apply/(free_in_congruence _ _ P'). 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LDelP => //. 
      by rewrite H.
      apply/LDelPObj => //.
      move:H5; apply/contra_not => Hyp'.
      by apply/(free_in_congruence _ P0). 
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LInSP => //. 
      by rewrite -H.
      by rewrite -H.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LInSP => //. 
      by rewrite H.
      by rewrite H.
Qed.


(* Useful Lemma *) 


Lemma lin_then_free {n : nat} : forall x (P : proc n),
    lin x P -> free_in x P.
Proof. 
  move => x P; elim: P x => /=.
  - move => n0 x H; inversion H.
  - move => n0 [i] P IH [j] H.
    inversion H; subst.
    by left. 
    by right; apply/IH.
  - move => n0 [i] P IH [j] H.
    inversion H; subst.
    by left. 
    by right; apply/IH.
  - move => n0 P IH [j] /= H.
    inversion H; subst. 
    by apply/IH.
  - move => n0 P IH1 Q IH2 [i] H.
    inversion H; subst. 
    by left; apply/IH1.
    by right; apply/IH2. 
  - move => n0 [i] P IH [j] /= H.
    inversion H; subst. 
    by right; apply/IH. 
  - move => n0 c c0 P IH x H.
    inversion H; subst. 
    by right; right; apply/IH.
    by right; left. 
Qed. 

Lemma lin_free_in_wait {n : nat} : forall x y (P Q : proc n.+2),
    lin x (y ! ․ P ∥ x ? ․ Q) -> ~(free_in x P \/ free_in x Q). 
Proof. 
  move => x y P Q H.
  inversion H; subst. 
  + move: H4. 
    apply/contra_not.
    by move => _ /=; left. 
  + inversion H4; subst => //. 
    move:H3 => /=.
    apply/contra_not. 
    case => //. 
    by right. 
Qed. 

Lemma lin_free_in_close {n : nat} : forall x y (P Q : proc n.+2),
    lin y (y ! ․ P ∥ x ? ․ Q) -> ~(free_in y P \/ free_in y Q). 
Proof. 
  move => x y P Q H.
  inversion H; subst. 
  + inversion H3; subst => //. 
    move:H4 => /=.
    apply/contra_not. 
    case => //. 
    by right. 
  + move: H3. 
    apply/contra_not.
    by move => _ /=; left. 
Qed. 






(* ---------------------------------------- *)

(* (vy) ( y <x.+2>. P   |   y(). Q )  *)

(* ==> (vy) ( P | Q [ scons x+.2 / 0 ] )  *)

(* ---------------------------------------- *)

(* lin x   (vy) ( y <x.+2>. P   |   y(). Q )  *)

(* -> *)

(* * lin x.+2  y<x.+2>. P  *)
(* * ~ ( free_in   x.+2   y().Q ) *)

(* ->  *)

(* * y != x.+2 *)
(* * ~ ( free_in x.+3 Q ) *)
(* * ~ ( free_in x.+2 P ) *)

(* ->  *)

(* How do we prove  *)
(*          lin x.+2 (Q [ scons x+.2 / 0 ] ) *)
(* ???  *)

(* Substitution Lemma will need  *)
(*     lin 0 Q *)
(* which we don't have unless we assume all_bound_lin. *)


(* Q =  use 0 | use 0 *)


(* EXTRA STUFF THAT NEEDS TO BE EVALUATED *) 


(* (* Linear Predicate using notfree_in *) *)
(* Inductive linearn {n : nat} : (ch n) -> proc n -> Prop := *)
(* | LEndPn  x            : linearn x EndP *)
(* | LWaitPn x P          : notfree_in x P -> *)
(*                          linearn x (WaitP x P) *)
(* | LWaitPcongrn x y P   : linearn y P -> *)
(*                          not (x = y) ->  *)
(*                          linearn y (WaitP x P) *)
(* | LClosePn x P         : notfree_in x P -> *)
(*                          linearn x (CloseP x P) *)
(* | LClosePcongrn x y P  : linearn y P ->  *)
(*                          not (x = y) ->  *)
(*                          linearn y (CloseP x P) *)
(* | LResPn  x P          : linearn (subst_ch (fun i => var_ch (shift (shift i))) x) *)
(*                            P -> *)
(*                          linearn x (ResP P) *)
(* | LParPLn x P1 P2      : linearn x P1 ->  *)
(*                          notfree_in x P2 -> *)
(*                          linearn x (ParP P1 P2) *)
(* | LParPRn x P1 P2      : notfree_in x P1 -> *)
(*                          linearn x P2 -> *)
(*                          linearn x (ParP P1 P2) *)
(* | LInSPn x y P         : linearn (subst_ch (fun i => var_ch (shift i)) y) P -> *)
(*                          linearn y (InSP x P) *)
(* | LDelPn x y z P       : not (z = y) -> *)
(*                          linearn z P ->  *)
(*                          linearn z (DelP x y P) *)
(* | LDelPObjn x y P      : not (x = y) ->  *)
(*                          notfree_in y P -> *)
(*                          linearn y (DelP x y P). *)

(* 
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer
*)

(* This works
From Hammer Require Import Hammer.
Lemma notin_fn_linear {n : nat} : forall (x : ch n) (P : proc n),
    notfree_in x P -> linearn x P.
    induction P; sauto lq: on .
    Qed.
*)

(* Lemma not_in_fn_linear {n : nat} : forall (x : ch n) (P : proc n), *)
(*     not (free_in x P) -> lin x P. *)
(* Proof. *)
(*   move => x P; elim: P x => //=. *)
(*   - constructor. *)
(*   - move => n0 [i] P IH [j] => /=. *)
(*     move/Decidable.not_or; case => H1 H2. *)
(*     apply/LWaitPcongr => //. *)
(*     by apply/IH.  *)
(*   - move => n0 [i] P IH [j] => /=. *)
(*     move/Decidable.not_or; case => H1 H2. *)
(*     apply/LClosePcongr => //. *)
(*     by apply/IH.  *)
(*   - move => n0 P IH [i] H. *)
(*     apply/LResP. *)
(*     apply/IH => //. *)
(*   - move => n0 P IH1 Q IH2 x. *)
(*     move/Decidable.not_or; case => H1 H2.  *)
(*     apply/LParPL => //. *)
(*     apply/IH1 => //. *)
(*   - move => n0 c P IH x.  *)
(*     move/Decidable.not_or; case => H1 H2.  *)
(*     apply/LInSP. *)
(*     apply/IH => //. *)
(*   - move => n0 c c0 P IH x.  *)
(*     move/Decidable.not_or; case => H1. *)
(*     move/Decidable.not_or; case => H2 H3. *)
(*     apply/LDelP => //. *)
(*     auto. *)
(*     apply/IH => //. *)
(* Qed.  *)


(* This predicate is required in the linearirty predicate reduction
proof for the communication (delegation) base case. In this case, we
need to ensure that the bound name, var_ch var_zero, in the
input—which will be substituted with the sent endpoint name—is also
linear. *)

(* Inductive all_bound_lin {n: nat} : proc n -> Prop := *)
(* | allbLNilP       : all_bound_lin EndP *)
(* | allbLWaitP x P  : all_bound_lin P -> all_bound_lin (WaitP x P) *)
(* | allbLCloseP x P : all_bound_lin P -> all_bound_lin (CloseP x P) *)
(* | allbLResP  P    : (* lin (var_ch var_zero) P -> lin (var_ch var_one) P -> *) *)
(*                      all_bound_lin P -> all_bound_lin (ResP P) *)
(* | allbLParP P1 P2 : all_bound_lin P1 -> all_bound_lin P2 ->  *)
(*                      all_bound_lin (ParP P1 P2) *)
(* | allbLInSP x P   : all_bound_lin P -> lin (var_ch var_zero) P ->  *)
(*                     all_bound_lin (InSP x P) *)
(* | allbLDelP x y P : all_bound_lin P -> all_bound_lin (DelP x y P) *)
(* . *)
(* (* *)

Lemma allbound_subst {n :nat} {m :nat} : forall P (sigma : fin n -> ch m), 
    all_bound_lin P -> all_bound_lin (subst_proc sigma P).
Proof. 
  move => P sigma; elim: P m sigma. 
  - constructor. 
  - move => n0 c P IH m sigma H => /=. 
    inversion H; subst. 
    constructor. 
    by apply/IH. 
  - move => n0 c P IH m sigma H => /=. 
    inversion H; subst. 
    constructor. 
    by apply/IH. 
  - move => n0 P IH m sigma H /=.
    inversion H; subst.    
    constructor.
    apply/(lin_subst var_zero) => //. 
    apply/injectiveNS_up_ch_ch_zero2.
    apply/(lin_subst var_one) => //.
    apply/injectiveNS_up_ch_ch_one.
    apply/IH => //.
  - move => n0 P IH1 Q IH2 m sigma H.
    inversion H; subst => /=.
    constructor. 
    by apply/IH1. 
    by apply/IH2. 
  - move => n0 c P IH m sigma H => /=.
    inversion H; subst. 
    constructor. 
    by apply/IH.
    apply/(lin_subst var_zero) => //.
    apply/injectiveNS_up_ch_ch_zero1.
  - move => n0 c c0 P IH m sigma H => /=.
    inversion H; subst. 
    constructor. 
    by apply/IH.
Qed. 

Lemma allbound_subst_inv {n :nat} {m :nat} : forall P (sigma : fin n -> ch m), 
    all_bound_lin (subst_proc sigma P) -> all_bound_lin P.
Proof. 
  move => P sigma; elim: P m sigma. 
  - constructor. 
  - move => n0 c P IH m sigma /= H.
    inversion H; subst. 
    constructor. 
    by apply/(IH _ sigma).
  - move => n0 c P IH m sigma /= H.
    inversion H; subst. 
    constructor. 
    by apply/(IH _ sigma).
  - move => n0 P IH m sigma H.
    inversion H; subst.    
    constructor.
    apply/lin_subst_inv => //.
    apply/H1. 
    apply/lin_subst_inv => //.
    apply/H2. 
    apply/IH.
    apply/H3.
  - move => n0 P IH1 Q IH2 m sigma H.
    inversion H; subst => /=.
    constructor. 
    move:H2.
    by apply/IH1. 
    move:H3.
    by apply/IH2. 
  - move => n0 c P IH m sigma H.
    inversion H;subst => /=.
    constructor. 
    apply/(IH _ (up_ch_ch sigma)). 
    by apply/H2. 
    apply/lin_subst_inv => //. 
    apply/H3.
  - move => n0 c c0 P IH m sigma H.
    inversion H; subst => /=.
    constructor. 
    by apply/(IH _ sigma).
Qed.

Lemma injectiveNS_zero_swap_zero_one {n : nat} : 
  forall (P : proc n.+2),
    injectiveNS var_zero P (swap_ch var_zero var_one).
Proof. 
  move => P; rewrite/injectiveNS => j H1 H2. 
  destruct j => //.
  destruct f => //. 
Qed. 

Lemma injectiveNS_one_swap_zero_one {n : nat} : 
  forall (P : proc n.+2),
    injectiveNS var_one P (swap_ch var_zero var_one).
Proof. 
  move => P; rewrite/injectiveNS => j H1 H2. 
  destruct j => //.
  move:H2. 
  rewrite/swap_ch. 
  destruct f => //. 
Qed. 

Lemma injectiveNS_zero_swap_zero_two {n : nat} : 
  forall (P : proc n.+4),
    injectiveNS var_zero P (swap_ch var_zero var_two).
Proof. 
  move => P; rewrite/injectiveNS => j H1 H2. 
  destruct j => //.
  destruct f => //. 
  destruct f => //. 
Qed. 


Lemma injectiveNS_two_swap_zero_two {n : nat} : 
  forall (P : proc n.+4),
    injectiveNS var_two
      (subst_proc (swap_ch var_zero var_two) P)
      (swap_ch var_one var_three).
Proof. 
  move => P; rewrite/injectiveNS => j H1 H2. 
  destruct j => //.
  destruct f => //. 
  destruct f => //. 
  destruct f => //. 
Qed. 

Lemma allbound_struct {n : nat } : forall {P Q : proc n}, 
    struct_eq P Q -> all_bound_lin P <-> all_bound_lin Q.
Proof. 
  move => P Q H; elim: H.
  - split. 
    move => H.
    inversion H; subst.
    by constructor. 
    move => H.
    inversion H; subst. 
    by constructor.
  - split. 
    move => H.
    inversion H; subst. 
    inversion H2; subst. 
    constructor.
    apply/H4. 
    by constructor. 
    move => H.
    inversion H; subst. 
    inversion H3; subst. 
    constructor. 
    by constructor. 
    apply/H5.
  - split.
    by move => H; inversion H.
    move => H. 
    constructor => //. 
    constructor. 
  - split.
    move => H.
    inversion H; subst. 
    inversion H2;subst. 
    constructor. 
    apply/LParPL => //.
    apply/free_ch_0_shift.
    constructor => //. 
    apply/free_ch_1_shift.     
    constructor => //.
    by repeat apply/allbound_subst.
    move => H.
    inversion H; subst. 
    inversion H3; subst. 
    constructor. 
    constructor. 
    inversion H1; subst => //. 
    by apply/not_in_fn_linear.
    inversion H2; subst => //.
    by apply/not_in_fn_linear.
    apply/H5. 
    apply (allbound_subst_inv _ (fun n => var_ch (shift (shift n)))).
    move:H6.
    rewrite/shift_two_up; asimpl.
    apply.
  - split.
    constructor. 
    repeat constructor.
  - split. 
    { 
      move => H. 
      inversion H; subst. 
      apply/allbLResP.
      apply/(lin_subst var_one _ _ (swap_ch var_zero var_one)) => //.
      apply/injectiveNS_one_swap_zero_one.
      apply/(lin_subst var_zero _ _ (swap_ch var_zero var_one)) => //.
      apply/injectiveNS_zero_swap_zero_one. 
      apply/allbound_subst => //. 
    } 
    {
      move => H. 
      inversion H; subst. 
      apply/allbLResP. 
      apply/(lin_subst_inv var_zero) => //.
      apply/H2.
      apply/(lin_subst_inv var_one) => //.
      apply/H1.
      apply/(allbound_subst_inv _ (swap_ch var_zero var_one)) => //.
    } 
  - split.
    {
      move => H.
      inversion H; subst. 
      inversion H1; subst. 
      inversion H2; subst. 
      inversion H3; subst. 
      simpl in * => {H H1 H2 H3}. 
      apply/allbLResP. 
      + apply/LResP => /=.
        apply (lin_subst var_two (var_ch var_two) _ 
                 (swap_ch var_one var_three)) => //.
        apply (lin_subst var_zero (var_ch var_two) _ 
                 (swap_ch var_zero var_two)) => //.
        apply/injectiveNS_zero_swap_zero_two.
        apply/injectiveNS_two_swap_zero_two.
      + apply/LResP => /=.
        apply (lin_subst var_one (var_ch var_three) _ 
                 (swap_ch var_one var_three)) => //.
        apply (lin_subst var_one (var_ch var_one) _ 
                 (swap_ch var_zero var_two)) => //.
        rewrite/injectiveNS => j H1 H2. 
        destruct j => //; destruct f => //; destruct f => //. 
        rewrite/injectiveNS => j H1 H2. 
        destruct j => //; destruct f => //; destruct f => //;
        destruct f => //. 
      + apply/allbLResP. 
        apply (lin_subst var_zero (var_ch var_zero) _ 
                 (swap_ch var_one var_three)) => //.
        apply (lin_subst var_two (var_ch var_zero) _ 
                 (swap_ch var_zero var_two)) => //.
        rewrite/injectiveNS => j H1 H2.
        destruct j => //; destruct f => //; destruct f => //.
        rewrite/injectiveNS => j H1 H2.
        destruct j => //; destruct f => //; destruct f => //.
        destruct f => //.
        apply (lin_subst var_three (var_ch var_one) _ 
                 (swap_ch var_one var_three)) => //.
        apply (lin_subst var_three (var_ch var_three) _ 
                 (swap_ch var_zero var_two)) => //.
        rewrite/injectiveNS => j H1 H2. 
        destruct j => //; destruct f => //; destruct f => //.
        destruct f => //.
        rewrite/injectiveNS => j H1 H2. 
        destruct j => //; destruct f => //; destruct f => //.
        destruct f => //.
        apply/allbound_subst.
        apply/allbound_subst => //.
    } 
    {
      move => H. 
      inversion H; subst. 
      inversion H1; subst. 
      inversion H2; subst. 
      inversion H3; subst. 
      simpl in * => {H H1 H2 H3}. 
      apply/allbLResP. 
      + apply/LResP => /=.
        apply/(lin_subst_inv var_two (var_ch var_zero) _ 
                 (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv var_zero (var_ch var_zero) _ 
                 (swap_ch var_one var_three)) => //. 
      + apply/LResP => /=.
        apply/(lin_subst_inv var_three (var_ch var_three) _ 
                 (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv var_three (var_ch var_one) _ 
                 (swap_ch var_one var_three)) => //. 
      + apply/allbLResP.
        apply/(lin_subst_inv var_zero (var_ch var_two) _ 
                 (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv var_two (var_ch var_two) _ 
                 (swap_ch var_one var_three)) => //. 
        apply/(lin_subst_inv var_one (var_ch var_one) _ 
                 (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv var_one (var_ch var_three) _ 
                 (swap_ch var_one var_three)) => //. 
        apply/allbound_subst_inv. 
        apply/allbound_subst_inv. 
        apply/H8.
     }
  - by [].
  - move => P0 Q0 Heq H.
    by apply iff_sym.
  - move => P0 Q0 R  Heq1 H1 Heq2 H2.
    by apply iff_trans.
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Admitted. 

*)
