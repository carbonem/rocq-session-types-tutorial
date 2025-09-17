(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import free_names synsem. 

(* Linear Predicate *)
Inductive lin {n : nat} : ch n -> proc n -> Prop :=
    LWaitP : forall (x : ch n) (P : proc n),
             ~(free_in x P) -> lin x (x ? ․ P)
  | LWaitPcongr : forall (x y : ch n) (P : proc n),
                  lin y P -> x <> y -> lin y (x ? ․ P)
  | LCloseP : forall (x : ch n) (P : proc n),
              ~(free_in x P) -> lin x (x ! ․ P)
  | LClosePcongr : forall (x y : ch n) (P : proc n),
                   lin y P -> x <> y -> lin y (x ! ․ P)
  | LResP : forall (x : ch n) (P : proc n.+2),
  lin ((shift \o shift ) x) P ->
            lin x ((ν) P)
  | LParPL : forall (x : ch n) (P1 P2 : proc n),
             lin x P1 ->
             ~(free_in x P2) -> lin x (P1 ∥ P2)
  | LParPR : forall (x : ch n) (P1 P2 : proc n),
             ~(free_in x P1) ->
             lin x P2 -> lin x (P1 ∥ P2)
  | LInSP : forall (x y : ch n) (P : proc n.+1),
            lin (shift  y) P ->
             lin y (x ? (_)․P)
  | LDelP : forall (x y z : ch n) (P : proc n),
            z <> y -> lin z P -> lin z (x ! y ․ P)
  | LDelPObj : forall (x y : ch n) (P : proc n),
               x <> y ->
               ~(free_in y P) -> lin y (x ! y ․ P).

Lemma lin_subst {n : nat} {m : nat} : 
  forall (x : ch n) y (P : proc n) (sigma : ren n m), 
    lin x P -> 
    injectiveNS x P sigma -> 
    y = sigma x -> (* this just makes it easier applyin IH *)
    lin y (subst_proc sigma P).
Proof. 
  move => x y P; elim: P m x y => /=.
  - by intros; inversion H.  
  (* WaitP *)
  - move => n0 c P IH m x y sigma => /= H1 => H2 H3.
    inversion H1; subst.
    * apply/LWaitP.
      move:H4.
      apply/contra_not. 
      move/(free_in_subst_inv _ sigma); apply.
      by move => j' Hyp; apply/H2 => /=; right.
    * apply/LWaitPcongr.
      apply/(IH _ x) => //.
      by move => y' Hyp; apply/H2 => /=; right.
      move: H6. 
      apply/contra_not => Hyp. 
      apply/Logic.eq_sym. 
      apply/H2; firstorder. 
  (* CloseP *)
  - move => n0 c P IH m x y sigma => /= H1 => H2 H3.
    inversion H1; subst.
    * apply/LCloseP.
      move:H4.
      apply/contra_not. 
      move/(free_in_subst_inv _ sigma); apply.
      by move => j' Hyp; apply/H2 => /=; right.
    * apply/LClosePcongr.
      apply/(IH _ x) => //.
      by move => y' Hyp; apply/H2 => /=; right.
      move: H6. 
      apply/contra_not => Hyp. 
      apply/Logic.eq_sym. 
      apply/H2; firstorder. 
  (* ResP *)
  - move => n0 P IH m x y sigma H1 H2 H3.
    inversion H1; subst.
    apply/LResP.
    apply/(IH _ (shift (shift x))) => //.
    by apply/injectiveNS_ResP.
  (* ParP *)
  - move => n0 P IH1 Q IH2 m x y sigma H1 H2 H3.
    inversion H1; subst. 
    * apply/LParPL.
      apply/(IH1 _ x) => //. 
      by apply/(injectiveNS_ParPL _ _ Q).
      move:H6.
      apply/contra_not => Hyp.
      apply/(free_in_subst_inv _ sigma) => //.
      by apply/(injectiveNS_ParPR _ P).
    * apply/LParPR.
      move:H5.
      apply/contra_not => Hyp.
      apply/(free_in_subst_inv _ sigma) => //.
      by apply/(injectiveNS_ParPL _ _ Q).
      apply/(IH2 _ x) => //. 
      by apply/(injectiveNS_ParPR _ P).
  (* InSP *) 
  - move => n0 c P IH m x y sigma H1 H2 H3. 
    inversion H1; subst. 
    apply/LInSP.
    apply/(IH _ (shift x)) => //.
    by apply/(injectiveNS_InSP _ c). 
  (* DelP *) 
  - move => n0 c c0 P IH m x y sigma H1 H2 H3. 
    inversion H1; subst.
    * apply/LDelP => /=.
      move:H5.
      apply/contra_not => Hyp.
      apply/H2 => //. 
      by right; left. 
      apply/(IH _ x) => //.
      by apply/(injectiveNS_DelSP _ ( c) ( c0)).
    * apply/LDelPObj.
      move:H5.
      apply/contra_not => Hyp.
      apply/Logic.eq_sym. 
      by apply/H2 => //=; left.
      move:H7.
      apply/contra_not.
      move/free_in_subst_inv. 
      apply.
      by apply/(injectiveNS_DelSP _ ( c) ( c0)).
Qed.


Lemma lin_key_subst {n : nat} : forall (y : ch n.+2) (P : proc n.+3), 
    lin zero P -> 
    ~( free_in (shift y) P) -> 
    lin y (subst_proc (scons y id_ren) P).
Proof.
  move => y P H1 H2. 
  apply/(lin_subst _ _ _ _ H1) => //. 
  move => y0 /=. 
  case: (ch_eq_dec (shift y) y0). 
  move => H3 H4 H5; subst.
  firstorder. 
  move => H3 H4 H5; subst.
  destruct y0 => //. 
  move : H5 => /=.
  rewrite/id_ren/shift => H; subst. 
  firstorder. 
Qed. 


Lemma lin_subst_inv {n : nat} {m : nat} : 
  forall (x : ch n) y (P : proc n) (sigma : ren n m), 
    lin y (subst_proc sigma P) ->
    injectiveNS x P sigma -> 
    y = sigma x -> (* this just makes it easier applyin IH *)
    lin x P.
Proof. 
  move => x y P sigma; elim: P m x y sigma => /=.
  - intros; inversion H.
  (* WaitP *)
  - move => n0 c P IH m x y sigma H1 HInj H2.
    inversion H1; subst.
    * have Hyp: x = c by apply/HInj => //; left.
      subst. 
      apply/LWaitP.
      move:H3.
      apply/contra_not.
      move/(free_in_subst _ sigma) => //.
    * apply/LWaitPcongr.
      apply/(IH _ x (sigma x) sigma) => //.
      move => j Hyp1 Hyp2.
      apply/HInj => //.
      by right. 
      move:H5.
      by apply/contra_not => ->.
  (* CLoseP *)
  - move => n0 c P IH m x y sigma H1 HInj H2.
    inversion H1; subst.
    * have Hyp: x = c by apply/HInj => //; left.
      subst. 
      apply/LCloseP.
      move:H3.
      apply/contra_not.
      move/(free_in_subst) => //.
    * apply/LClosePcongr.
      apply/(IH _ x (sigma x) sigma) => //.
      move => j Hyp1 Hyp2.
      apply/HInj => //.
      by right. 
      move:H5.
      by apply/contra_not => ->.
  (* ResP *)
  - move => n0 P IH m x y sigma H1 HInj H2.
    inversion H1; subst. 
    apply/LResP. 
    apply/(IH _ (shift (shift x)) (shift (shift (sigma x))) 
             (up_ch (up_ch sigma))) => //=.
    by apply/injectiveNS_ResP.
  (* ParP *)
  - move => n0 P IH1 Q IH2 m x y sigma H1 HInj H2.
    inversion H1; subst. 
    * apply/LParPL.
      apply/(IH1 _ x (sigma x)) => //. 
      apply/H4.
      apply/(injectiveNS_ParPL _ _ Q) => //.
      move:H5.
      apply/contra_not.
      move/(free_in_subst _ sigma) => //.
    * apply/LParPR.
      move:H4.
      apply/contra_not.
      move/(free_in_subst _ sigma) => //.
      apply/(IH2 _ x (sigma x)) => //. 
      apply/H5.
      apply/(injectiveNS_ParPR _ P) => //.
  (* InSP *)
  - move => n0 c P IH m x y sigma H1 HInj H2. 
    inversion H1; subst. 
    apply/LInSP => /=.
    apply/(IH _ _ (shift (sigma x)) (up_ch sigma)) => //.
    apply/(injectiveNS_InSP _ c) => //.
  (* DelP *)
  - move => n0 c c0 P IH m x y sigma H1 HInj H2. 
    inversion H1; subst. 
    + apply/LDelP.
      move:H4. 
      by apply/contra_not => ->. 
      apply/(IH _ _ (sigma x) sigma) => //.
      by apply/(injectiveNS_DelSP _ c c0).
    + (* need to prove that i = k0 *)
      have fact : x = c0.
      apply/HInj => //.
      by right; left.
      subst. 
      apply/LDelPObj.
      move:H4.
      by apply/contra_not => ->.
      move:H6.
      by apply/contra_not => /(free_in_subst _ sigma). 
Qed. 

   
Lemma lin_congruence {n : nat} : forall {x : ch n} P Q,
    struct_eq P Q -> lin x P <-> lin x Q.
Proof.
  move => x P Q H; elim: H x => //.
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
        move/(free_in_subst_inv _ (fun x => shift (shift x))).
        apply.
        apply/injectiveNS_shift_shift.
      + apply/LResP.
        apply LParPR. 
        move : H3 => //=. 
        apply/lin_subst => //.
        apply/H4.
        apply/injectiveNS_shift_shift.
    }
    { move => H.
      inversion H => {H}; subst. 
      inversion H2 => {H2}; subst. 
      + apply/LParPL. 
        apply/LResP => //.
        move:H4 => /=.
        apply/contra_not => Hyp.
        apply/(free_in_subst) => //=.
      + apply/LParPR => //=.
        apply/(lin_subst_inv _ (shift (shift x)) _
                 (fun w =>  (shift (shift w)))) => //.
        move => z _.
        by case.
    }
  - move => n0 R x. (* swapC *) 
    split. 
    {
      move => H. 
      inversion H;subst. 
      constructor => /=.
      apply/(lin_subst (shift(shift x)) _ _ (swap_ch zero one)) => //.
      apply/injectiveNS_swap.
    }
    {
      move => H.
      inversion H; subst. 
      constructor. 
      apply/(lin_subst_inv (shift(shift x)) _ _
               (swap_ch zero one)) => //.
      apply/H2. 
      apply/injectiveNS_swap.
    } 
  - move => n0. (* swapB *)
    split.
    {
      move => H.
      inversion H;subst. 
      inversion H2;subst. 
      constructor; constructor => /=.
      apply/(lin_subst (shift (shift (shift (shift x))))) => //.
      apply/(lin_subst (shift (shift (shift (shift x))))) => //.
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
    }
    {
      move => H. 
      inversion H; subst. 
      inversion H2; subst. 
      constructor. 
      constructor => /=. 
      apply (lin_subst_inv (shift( shift (shift (shift x))))
               ((swap_ch zero two) (shift( shift (shift (shift x)))))
               _ (swap_ch zero two)) => //.
      apply (lin_subst_inv 
               ((swap_ch zero two) (shift( shift (shift (shift x)))))
               ((swap_ch one three)
                  ((swap_ch zero two)
                     (shift( shift (shift (shift x))))))
               _ (swap_ch one three)) => //.
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
    }
  - split.
    move => H.
    inversion H; subst.
    inversion H2.
    move => H.
    inversion H.     
  - move => n0 P0 Q0 H1 H2 x. 
    by apply iff_sym.
  - move => n0 P0 Q0 R Heq H1 Heq2 H2 x.
    firstorder. 
  - move => n0 P0 P' Q0 Q' Heq1 H1 Heq2 H2 i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LParPL.
      firstorder. 
      move: H5; apply/contra_not => Hyp'. 
      by apply/(free_in_congruence _ _ Q'). 
      apply/LParPR. 
      move: H4; apply/contra_not => Hyp'. 
      by apply/(free_in_congruence _ _ P'). 
      firstorder.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LParPL. 
      firstorder.
      move: H5; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ Q0) => //. 
      apply/LParPR. 
      move: H4; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //. 
      firstorder. 
  - move => n0 P0 P' Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LResP. 
      firstorder.
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LResP. 
      firstorder. 
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LCloseP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ _ P') => //.
      apply/LClosePcongr => //.
      firstorder. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LCloseP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //.
      apply/LClosePcongr => //.
      firstorder. 
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LWaitP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ _ P') => //.
      apply/LWaitPcongr => //.
      firstorder. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LWaitP. 
      move: H2; apply/contra_not => Hyp'. 
      apply/(free_in_congruence _ P0) => //.
      apply/LWaitPcongr => //.
      firstorder. 
  - move => n0 P0 P' x y Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LDelP => //. 
      firstorder. 
      apply/LDelPObj => //.
      move:H5; apply/contra_not => Hyp'.
      by apply/(free_in_congruence _ _ P'). 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LDelP => //. 
      firstorder. 
      apply/LDelPObj => //.
      move:H5; apply/contra_not => Hyp'.
      by apply/(free_in_congruence _ P0). 
  - move => n0 P0 P' x Heq H i.
    split. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LInSP => //. 
      firstorder. 
    * move => Hyp.
      inversion Hyp; subst. 
      apply/LInSP => //. 
      firstorder. 
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


