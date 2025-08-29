(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
From Coq Require Import FunctionalExtensionality.
(* Require Import Stdlib.Program.Equality. *)
Require Import free_names types semantics syntax fintype core linearity_predicate env.


(* Some extra injectiveNS properties that we may remove if we go into injectiveS instead *) 

Lemma injectiveNS_scons_shift_var_zero {n : nat} : forall x P,
    not(x=var_ch var_zero) -> 
    injectiveNS (@shift n.+2 var_zero) P (scons x ids).
Proof.
  move => x P H1.
  rewrite/injectiveNS/shift/scons => j H2 => /=. 
  destruct j.
  destruct f => //.
  destruct x; destruct f => //.
Qed. 


Lemma injectiveNS_scons_shift_var_one {n : nat} : forall x P,
    not(x=var_ch var_one) -> 
    injectiveNS (@shift n.+2 var_one) P (scons x ids).
Proof.
  move => x P H1.
  rewrite/injectiveNS/shift/scons => j H2 => /=. 
  destruct j.
  destruct f => //.
  destruct x; destruct f => //.
  simpl.
  move => H; subst. 
  by move:H1; case.  
Qed. 
  
Notation "x '!->' v ';' m" := (update m x v)
                              (at level 100, v at next level, right associativity).
(* Typing rules *)
Reserved Notation "Delta ⊢ P"  (at level 40).

(* StartTY *)
Inductive OFT {n : nat} (Delta : env n) : proc n -> Prop :=  
    TEndP : Delta ⊢ ∅
  | TParP : forall P1 P2 : proc n,
            Delta ⊢ P1 -> Delta ⊢ P2 -> Delta ⊢ (P1 ∥ P2)
  | TResP : forall (T : sType) (P : proc n.+2),
            (free_in (n.+2__ch var_zero) P ->
             lin (n.+2__ch var_zero) P) ->
            (free_in (n.+2__ch var_one) P ->
             lin (n.+2__ch var_one) P) ->
            (T ::: (dual T ::: Delta)) ⊢ P ->
            Delta ⊢ ((ν) P)
  | TWaitP : forall (x : ch n) (P : proc n),
             Delta x = end? ->
             Delta ⊢ P -> Delta ⊢ (x ? ․ P)
  | TCloseP : forall (x : ch n) (P : proc n),
              Delta x = end! ->
              Delta ⊢ P -> Delta ⊢ (x ! ․ P)
  | TInSP : forall (x : ch n) (T' T : sType) (P : proc n.+1),
            Delta x = ? T ․ T' ->
            lin (n.+1__ch var_zero) P ->
            (T ::: (x !-> T'; Delta)) ⊢ P ->
            Delta ⊢ (x ? (_)․P)
  | TDelP : forall (x y : ch n) (T' T : sType) (P : proc n),
            Delta x = ! T ․ T' ->
            Delta y = T ->
            (x !-> T'; Delta) ⊢ P ->
            Delta ⊢ (x ! y ․ P)
            where  "Delta ⊢ P" := (OFT Delta P).
            
(* EndTY *)
(*
| TEndP : OFT Delta EndP

| TParP P1 P2: 
  (* ˆˆˆˆˆˆˆˆ^ *)
  OFT Delta P1 ->
  OFT Delta P2 ->
  (* ------------------- *)
  OFT Delta (ParP P1 P2)

| TResP T P:
  (* ˆˆˆˆˆˆˆˆ^ *)
  (free_in (var_ch var_zero) P -> lin (var_ch var_zero) P) ->
  (free_in (var_ch var_one) P -> lin (var_ch var_one) P) -> 
  OFT (shift_env T (shift_env (dual T) Delta)) P -> 
  (* ------------------- *)
  OFT Delta (ResP P)

| TWaitP x P: 
  (* ˆˆˆˆˆˆˆˆ^ *)
  Delta x = WaitT -> 
  OFT Delta P -> 
  (* ------------------------- *)
  OFT Delta (WaitP x P)

| TCloseP  x P: 
  (* ˆˆˆˆˆˆˆˆ^ *)
  Delta x = CloseT -> 
  OFT Delta P -> 
  (* -------------------------- *)
  OFT Delta (CloseP x P)

| TInSP  x T' T P:
  (* ˆˆˆˆˆˆˆˆ^ *)
  Delta x = (InST T T') ->  
  lin (var_ch var_zero) P -> 
  OFT (shift_env T (update Delta x T')) P -> 
  (* ------------------------------------*)
  OFT Delta (InSP x P)

| TDelP x y T' T P: 
  (* ˆˆˆˆˆˆˆˆ^ *)
  Delta x = (OutST T T') ->  
  Delta y = T ->  
  OFT (update Delta x T') P -> 
  (* ---------------------------------------*)
  OFT Delta (DelP x y P).

Notation "Γ ⊢ P" := (OFT Γ P) (at level 40).

*)

Lemma substitution {n m : nat} : forall (Delta: env n) (Gamma: env m) sigma P,
    injectiveS P sigma -> 
    ltc Delta Gamma sigma P -> OFT Delta P -> OFT Gamma (subst_proc sigma P).
Proof. 
  move => Delta Gamma sigma P; elim: P m Delta Gamma sigma.
  - constructor. 
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/TWaitP.
    rewrite -H2; symmetry; apply/Hltc => /=.
    by left.
    apply/(IH _ Delta) => //.
    rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
    apply/Hinj => //=.
    by right. 
    by right. 
    by apply/(ltc_WaitP _ (var_ch i)). 
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/TCloseP.
    rewrite -H2; symmetry; apply/Hltc => /=.
    by left.
    apply/(IH _ Delta) => //.
    rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
    apply/Hinj => //=.
    by right. 
    by right. 
    by apply/(ltc_CloseP _ (var_ch i)). 
  - move => n0 P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/(TResP _ T).
    * move => Hyp.
      apply/lin_subst.
      apply/H1. 
      apply/free_in_subst.
      apply/Hyp.
      apply/injectiveNS_up_ch_ch_zero2.
      apply/injectiveNS_up_ch_ch_zero2.
      by simpl.
    * move => Hyp.
      apply/lin_subst. 
      apply/H2. 
      apply/free_in_subst. 
      apply/Hyp.
      apply/injectiveNS_up_ch_ch_one.
      apply/injectiveNS_up_ch_ch_one.
      by simpl.
    * apply (IH _ (shift_env T (shift_env (dual T) Delta))
               (shift_env T (shift_env (dual T) Gamma))) => //.
      apply/injectiveS_ResP => //.
      apply/ltc_ResP => //.
  - move => n0 P IH1 Q IH2 m2 Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    constructor.
    + apply/(IH1 _ Delta) => //.
      rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
      apply/Hinj => //=.
      by left.
      by left. 
      by apply/(ltc_ParPL _ _ Q).
    + apply/(IH2 _ Delta) => //.
      rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
      apply/Hinj => //=.
      by right.
      by right.
      by apply/(ltc_ParPR _ P).
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/(TInSP _ _ T' T).
    rewrite -H2. 
    symmetry.
    by apply/Hltc => /=; left. 
    apply/lin_subst.
    apply/H3. 
    apply/injectiveNS_up_ch_ch_zero1. 
    by simpl.
    apply/(IH _ (shift_env T (update Delta (var_ch i) T'))) => //.
    apply/(injectiveS_InSP (var_ch i)) => //.
    apply (ltc_InSP _ _ (var_ch i)). 
    apply/ltc_update => //=. (* here use injectiveS *)
    by left. 
  - move => n0 [i] [j] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply (TDelP _ _ _ T' (Delta (var_ch j))).
    rewrite -H3. 
    symmetry.
    apply Hltc => /=.
    by left. 
    symmetry.
    apply/Hltc => //=.
    by right; left. 
    apply/(IH _ (update Delta (var_ch i) T')) => //.
    apply/(injectiveS_DelP (var_ch i) (var_ch j)) => //.
    apply/(ltc_DelP _ (var_ch i) (var_ch j)).
    apply/ltc_update => //=. (* here use injectiveS *)
    by left.
Qed. 

Lemma substitution_inv {n m : nat} : forall (Delta: env n) (Gamma: env m) sigma P,
    injectiveS P sigma -> 
    ltc Delta Gamma sigma P -> OFT Gamma (subst_proc sigma P) -> OFT Delta P.
Proof. 
  move => Delta Gamma sigma P; elim: P m Delta Gamma sigma.
  - constructor. 
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/TWaitP.
    rewrite -H2; apply/Hltc => /=.
    by left.
    apply/(IH _ _ Gamma sigma) => //. 
    rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
    apply/Hinj => //=.
    by right. 
    by right. 
    by apply/(ltc_WaitP _ (var_ch i)). 
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/TCloseP.
    rewrite -H2; apply/Hltc => /=.
    by left.
    apply/(IH _ _ Gamma sigma) => //. 
    rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
    apply/Hinj => //=.
    by right. 
    by right. 
    by apply/(ltc_WaitP _ (var_ch i)). 
  - move => n0 P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/(TResP _ T).
    * move/(free_in_subst_inv _ (up_ch_ch (up_ch_ch sigma))) => Hyp. 
      apply/lin_subst_inv => //.
      apply/H1 => //. 
      apply/injectiveNS_up_ch_ch_zero2.
    * move/(free_in_subst_inv _ (up_ch_ch (up_ch_ch sigma))) => Hyp. 
      apply/lin_subst_inv => //.
      apply/H2 => //. 
      apply/injectiveNS_up_ch_ch_one.
    * apply (IH _ (shift_env T (shift_env (dual T) Delta))
               (shift_env T (shift_env (dual T) Gamma)) 
            (up_ch_ch (up_ch_ch sigma))) => //.
      apply/injectiveS_ResP => //.
      apply/ltc_ResP => //.
  - move => n0 P IH1 Q IH2 m2 Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    constructor.
    + apply/(IH1 _ Delta Gamma sigma) => //.
      rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
      apply/Hinj => //=.
      by left.
      by left. 
      by apply/(ltc_ParPL _ _ Q).
    + apply/(IH2 _ Delta Gamma sigma) => //.
      rewrite/injectiveS => i0 j Hyp1 Hyp2 Hyp3.
      apply/Hinj => //=.
      by right.
      by right.
      by apply/(ltc_ParPR _ P).
  - move => n0 [i] P IH m Delta Gamma sigma Hinj Hltc H.
    inversion H; subst. 
    apply/(TInSP _ _ T' T).
    rewrite -H2. 
    by apply/Hltc => /=; left. 
    apply/(lin_subst_inv _ (var_ch var_zero) _ (up_ch_ch sigma)) => //.
    apply/injectiveNS_up_ch_ch_zero1. 
    apply/(IH _ (shift_env T (update Delta (var_ch i) T')) 
             (shift_env T (update Gamma (sigma i) T')) (up_ch_ch sigma)) => //.
    apply/(injectiveS_InSP (var_ch i)) => //.
    apply (ltc_InSP _ _ (var_ch i)). 
    apply/ltc_update => //=. (* here use injectiveS *)
    by left. 

  - move => n0 [i] [j] P IH m Delta Gamma sigma Hinj Hltc H => /=.
    inversion H; subst. 
    apply/(TDelP _ _ _ T' (Gamma (sigma j))).
    rewrite -H3. 
    apply Hltc => /=.
    by left. 
    apply/Hltc => //=.
    by right; left. 

    apply/(IH _ _ (update Gamma (sigma i) T') sigma) => //.
    apply/(injectiveS_DelP (var_ch i) (var_ch j)) => //.
    apply/(ltc_DelP _ (var_ch i) (var_ch j)).
    apply/ltc_update => //=. (* here use injectiveS *)
    by left.
Qed. 


Theorem subject_congruence : forall n P Q Delta,
    @struct_eq n P Q -> OFT Delta P <-> OFT Delta Q. 
Proof.
  move => n P Q Delta H; elim: H Delta => //.

  - split. (* SC_Par_Com *)
    move => H.
    inversion H; subst. 
    constructor => //. 
    move => H. 
    inversion H; subst. 
    constructor =>//. 

  - split. (* SC_Par_Assoc *)
    move => H. 
    inversion H; subst.
    inversion H2; subst. 
    constructor =>//. 
    constructor =>//. 
    move => H. 
    inversion H; subst.
    inversion H3; subst. 
    constructor =>//. 
    constructor =>//. 

  - split. (* SC_Par_Inact *)
    move => H; inversion H =>//.
    move => H. 
    constructor => //. 
    constructor. 

  - split. (* SC_Res_Scope *)
    { move => H.
      inversion H; subst. 
      inversion H2; subst.
      apply (TResP _ T) => /=. 
      + case. 
        move/H1 => Hlin0.
        apply/LParPL => //.
        apply/free_in_0_shift.
        by move/free_in_0_shift.
      + case. 
        move/H4 => Hlin1.
        apply/LParPL => //.
        apply/free_in_1_shift.
        by move/free_in_1_shift.       
      + apply/TParP => //.
        (* now we prove Delta ⊢ Q0 implies 
           shift_env T (shift_env (dual T) Delta) ⊢ shift_two_up Q0
         *)
        apply/substitution => //. (* Note: shift_two_up is injective *) 
        by rewrite/injectiveS => i j _ _; rewrite/shift; case.
    } 
    { 
      move => H'.
      inversion H'; subst => {H'}. 
      inversion H2; subst => {H2}. 
      apply/TParP.
      + apply (TResP _ T) => //.
        * move => Hyp.
          have : free_in (n0.+2__ch var_zero) (P0 ∥ shift_two_up Q0)
            by left. 
          move/H0 => HLin0.
          inversion HLin0; subst => //.
        * move => Hyp.
          have : free_in (n0.+2__ch var_one) (P0 ∥ shift_two_up Q0)
            by left. 
          move/H1 => HLin1.
          inversion HLin1; subst => //.
      + move:H5 => /(substitution_inv _ _) => //.
        apply => //.
        rewrite/injectiveS => i0 j Hyp1 Hyp2.
        by case => ->.
    }

  - split. (* SC_Res_SwapC *) 
    {
      move => H. 
      inversion H; subst. 
      apply/(TResP _ (dual T)).
      * move => Hyp.
        apply/lin_subst. 
        apply/H2.
        apply/(free_in_subst _ (swap_ch var_zero var_one)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        auto. 
      * move => Hyp.
        apply/lin_subst. 
        apply/H1.
        apply/(free_in_subst _ (swap_ch var_zero var_one)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        auto. 
      * apply (substitution (shift_env T (shift_env (dual T) Delta))) => //. 
        apply/injectiveS_swap.
        have fact : 
          (shift_env (dual T) (shift_env (dual (dual T)) Delta)) =
            (swap_env (shift_env T (shift_env (dual T) Delta)) 
               (var_ch var_zero) (var_ch var_one)).
        { rewrite dual_dual_is_identity.
          apply functional_extensionality => x.
          rewrite/swap_env/shift_env.
          case: ifP.
          move/eqP => -> //.
          move/eqP => Hyp.
          case: ifP.
          move/eqP => -> //.
          move/eqP => Hyp'.
          destruct x => //.
          destruct f => //.
          destruct f => //. } 
        rewrite fact. 
        apply/ltc_swap => //.
    }
    {
      move => H. 
      inversion H; subst. 
      apply/(TResP _ (dual T)). 
      - move => Hyp.
        apply/(lin_subst_inv _ (var_ch var_one) _ (swap_ch var_zero var_one)) => //.
        apply/H2. 
        move: Hyp.
        by move/(free_in_subst_inv _ (swap_ch var_zero var_one)).
        apply/injectiveNS_swap.
      - move => Hyp.
        apply/(lin_subst_inv _ (var_ch var_zero) _ 
                 (swap_ch var_zero var_one)) => //.
        apply/H1. 
        move: Hyp.
        by move/(free_in_subst_inv _ (swap_ch var_zero var_one)).
        apply/injectiveNS_swap.
      - apply/(substitution_inv _ (shift_env T (shift_env (dual T) Delta))
                 (swap_ch var_zero var_one)) => //.
        + apply/injectiveS_swap.
        + apply/ltc_swap.
          apply/functional_extensionality => x.
          rewrite/swap_env/shift_env. 
          case: ifP.
          move/eqP => ->. 
          by rewrite dual_dual_is_identity.
          move/eqP => Hyp.
          case: ifP.
          by move/eqP => ->.
          move/eqP => Hyp'.
          destruct x => //.
          destruct f => //.
          destruct f => //.
    }

  - split. (* SC_Res_SwapB *) 
    { 
      move => H. 
      inversion H; subst. 
      inversion H3; subst.
      apply/(TResP _ T0).
      * move => /= Hyp.
        apply/LResP => /=.
        have:  free_in (n0.+4__ch var_zero) P0. 
        { 
          apply/(free_in_subst _ (swap_ch var_zero var_two)). 
          apply/(free_in_subst _ (swap_ch var_one var_three)). 
          apply/Hyp.
          apply/injectiveNS_swap.
          apply/injectiveNS_swap.
        }
        move/H4 => H'.
        apply/(lin_subst (shift (shift var_zero))) => //.
        apply/(lin_subst var_zero) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      * move => /= Hyp.
        apply/LResP => /=.
        have:  free_in (n0.+4__ch var_one) P0. 
        { apply/(free_in_subst _ (swap_ch var_zero var_two)). 
          apply/(free_in_subst _ (swap_ch var_one var_three)) => //. 
          apply/injectiveNS_swap.
          apply/injectiveNS_swap. }
        move/H5 => H'.
        apply/(lin_subst var_one) => //.
        apply/(lin_subst var_one) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      * apply/(TResP _ T).
        + move => /= Hyp. 
          have : free_in (n0.+4__ch (shift (shift var_zero))) P0. 
          { apply/(free_in_subst _ (swap_ch var_zero var_two)). 
            apply/(free_in_subst _ (swap_ch var_one var_three)) => //.
            apply/injectiveNS_swap.
            apply/injectiveNS_swap. }
          move/H1 => H'.
          inversion H'; subst. 
          apply/(lin_subst var_zero) => //.
          apply/lin_subst. 
          apply/H8.
          apply/injectiveNS_swap.
          by rewrite/var_zero.
          apply/injectiveNS_swap.
        + move => /= Hyp. 
          have : free_in (n0.+4__ch (shift (shift var_one))) P0. 
          { apply/(free_in_subst _ (swap_ch var_zero var_two)). 
            apply/(free_in_subst _ (swap_ch var_one var_three)) => //.
            apply/injectiveNS_swap.
            apply/injectiveNS_swap. }
          move/H2 => H'.
          inversion H'; subst. 
          apply/(lin_subst var_three) => //.
          apply/lin_subst. 
          apply/H8.
          apply/injectiveNS_swap.
          by rewrite/var_one.
          apply/injectiveNS_swap.
        + apply (substitution 
                   (shift_env T
                      (shift_env (dual T0) 
                         (shift_env T0 
                            (shift_env (dual T) Delta))))
            ).
          - apply/injectiveS_swap. 
          - apply/ltc_swap.
            apply/functional_extensionality => [x].
            destruct x => //.
            rewrite/swap_env/shift_env.
            case: ifP.
            move/eqP; case => -> //.
            move/eqP => Hyp.
            destruct f => //.
            destruct f => //.
            destruct f => //.
            destruct f => //.
          - apply/(substitution 
                     (shift_env T0
                      (shift_env (dual T0) 
                         (shift_env T
                            (shift_env (dual T) Delta))))) => //.
            apply/injectiveS_swap.
            apply/ltc_swap.
            apply/functional_extensionality => [x].
            destruct x => //.
            rewrite/swap_env/shift_env. 
            case: ifP. 
            move/eqP; case => -> //.
            move/eqP => Hyp.
            destruct f => //.
            destruct f => //.
            destruct f => //.
    }
    { 
      move => H.
      inversion H; subst => {H}.
      inversion H3; subst => {H3}.
      apply/(TResP _ T0).
      
      + move/(free_in_subst_inv _ (swap_ch var_zero var_two)).
        move/(free_in_subst_inv _ (swap_ch var_one var_three)).
        move/H0 => Hyp.
        apply/LResP.
        apply/(lin_subst_inv _ _ _ (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv _ _ _ (swap_ch var_one var_three)) => //.
        apply/Hyp.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.

      + move/(free_in_subst_inv _ (swap_ch var_zero var_two)).
        move/(free_in_subst_inv _ (swap_ch var_one var_three)).
        move/H4 => Hyp.
        apply/LResP.
        apply/(lin_subst_inv _ _ _ (swap_ch var_zero var_two)) => //. 
        apply/(lin_subst_inv _ _ _ (swap_ch var_one var_three)) => //.
        apply/Hyp.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.

      + apply/(TResP _ T).
        * move/(free_in_subst_inv _ (swap_ch var_zero var_two)).
          move/(free_in_subst_inv _ (swap_ch var_one var_three)).
          move/H1 => Hyp.
          inversion Hyp; subst. 
          apply/(lin_subst_inv _ _ _ (swap_ch var_zero var_two)) => //.
          apply/(lin_subst_inv _ (var_ch var_two) _ (swap_ch var_one var_three)) => //.
          apply/injectiveNS_swap.
          apply/injectiveNS_swap.
        * move/(free_in_subst_inv _ (swap_ch var_zero var_two)).
          move/(free_in_subst_inv _ (swap_ch var_one var_three)).
          move/H2 => Hyp.
          inversion Hyp; subst. 
          apply/(lin_subst_inv _ _ _ (swap_ch var_zero var_two)) => //.
          apply/(lin_subst_inv _ (var_ch var_three) _ (swap_ch var_one var_three)) => //.
          apply/injectiveNS_swap.
          apply/injectiveNS_swap.

        * apply/(substitution_inv _ 
                   (shift_env T0 (shift_env (dual T) 
                                   (shift_env T (shift_env (dual T0) Delta))))
                   (swap_ch var_zero var_two)). 
          apply/injectiveS_swap.
          apply/ltc_swap.
          apply/functional_extensionality => [x].
          destruct x => //.
          rewrite/swap_env/shift_env.
          case: ifP.
          move/eqP; case => -> //.
          move/eqP => Hyp.
          destruct f => //.
          destruct f => //.
          destruct f => //.
          apply/(substitution_inv _ 
                   (shift_env T0 (shift_env (dual T0) 
                                   (shift_env T (shift_env (dual T) Delta))))
                   (swap_ch var_one var_three)) => //. 
          apply/injectiveS_swap.
          apply/ltc_swap.
          apply/functional_extensionality => [x].
          destruct x => //.
          rewrite/swap_env/shift_env.
          case: ifP.
          move/eqP; case => -> //.
          move/eqP => Hyp.
          destruct f => //.
          destruct f => //.
          destruct f => //.
          destruct f => //.
    }

  (* SC_Res_Zero *)
  - split.
    move => H.
    constructor.
    move => H.
    apply (TResP _ end?).
    case. 
    case. 
    constructor.
    
  (* SC_Refl *) 
  - move => n0 P0 Q0 Hstruct IH Delta.
    by apply iff_sym.
    
    
  (* SC_Sym *) 
  - move => n0 P0 Q0 R Heq1 H1 Heq2 H2 Delta.
    move: (H1 Delta) (H2 Delta); apply iff_trans.

  (*  SC_Trans *)
  - move => n0 P0 P' Q0 Q' Heq1 H1 Heq2 H2 Delta.
    move: (H1 Delta) (H2 Delta) => H1' H2'.
    split.
    * move => H.
      inversion H; subst.
      apply/TParP.
      by apply/H1'.
      by apply/H2'.
    * move => H.
      inversion H; subst.
      apply/TParP.
      by apply/H1'.
      by apply/H2'.

  (* SC_Cong_Res *) 
  - split.
    * move => Hyp.
      inversion Hyp; subst.
      apply/(TResP _ T).
      move => Hyp'.
      apply/(lin_congruence P0) => //.
      apply/H2.
      by apply/(free_in_congruence _ _ P').
      move => Hyp'.
      apply/(lin_congruence P0) => //.
      apply/H3.
      by apply/(free_in_congruence _ _ P').
      by apply/H0.
    * move => Hyp.
      inversion Hyp; subst.
      apply/(TResP _ T).
      move => Hyp'. 
      apply/(lin_congruence _ P') => //.
      apply/H2. 
      by apply/(free_in_congruence _ P0).
      move => Hyp'. 
      apply/(lin_congruence _ P') => //.
      apply/H3. 
      by apply/(free_in_congruence _ P0).
      by apply/H0.

  (* SC_Cong_Close *)
  - split.
    * move => Hyp.
      inversion Hyp; subst.
      apply/TCloseP => //.
      by apply/H0.
    * move => Hyp.
      inversion Hyp; subst.
      apply/TCloseP => //.
      by apply/H0.

  (* SC_Cong_Wait *)
  - split.
    * move => Hyp.
      inversion Hyp; subst.
      apply/TWaitP => //.
      by apply/H0.
    * move => Hyp.
      inversion Hyp; subst.
      apply/TWaitP => //.
      by apply/H0.

  (* SC_Cong_OutS *)
  - split.
    * move => Hyp.
      inversion Hyp; subst.
      apply (TDelP _ _ _ T' (Delta y)) => //.
      by apply/H0.
    * move => Hyp.
      inversion Hyp; subst.
      apply (TDelP _ _ _ T' (Delta y)) => //.
      by apply/H0.

  (* SC_Cong_InsP *) 
  - split.
    * move => Hyp.
      inversion Hyp; subst.
      apply (TInSP _ _ T' T) => //.
      by apply/(lin_congruence P0).
      by apply/H0.
    * move => Hyp.
      inversion Hyp; subst.
      apply (TInSP _ _ T' T) => //.
      by apply/(lin_congruence _ P').
      by apply/H0.
Qed. 



Lemma lin_reduction {n : nat} : forall (x : ch n) (P Q : proc n) Delta,
    reduce P Q -> OFT Delta P -> lin x P -> lin x Q.
Proof.
  move => x P Q Delta H; elim: H x Delta.
  (* *) 
  - move => n0 P0 Q0 Hred IH x Delta H.
    inversion H; constructor; subst => {H}.
    apply/(IH _ (shift_env T (shift_env (dual T) Delta))) => //.
    by inversion H4; subst. 
  (* *) 
  - move => n0 P0 Q0 R Hred IH x Delta HDelta H. 
    inversion H; subst. 
    + apply/LParPL => //. 
      apply/IH => //. 
      inversion HDelta; subst. 
      apply/H2. 
    + apply/LParPR => //. 
      move:H3; apply/contra_not. 
      apply/free_in_reduction => //.
  (* *) 
  - move => n0 P0 P' Q0 Q' Heq1 Hred IH Heq2 x Delta HDelta H. 
    apply/(lin_congruence Q') => //. 
    apply/(IH _ Delta) => //.
    apply/(subject_congruence _ P0) => //. 
    apply/(lin_congruence P0) => //. 
  (* *) 
  - move => n0 P0 Q0 [i] Delta HDelta H.
    inversion H; subst => {H}.
    apply/LResP.
    inversion H2; subst => {H2}. 
    + (* LParL *)
      apply/LParPL => /=.
      inversion H3; subst => {H3}.
      apply/H2. 
      move:H4 => /=.
      apply/contra_not. 
      by right. 
    + (* LParR *)
      apply/LParPR => /=.
      move: H3 => /=.
      apply/contra_not. 
      by right. 
      inversion H4; subst => {H4}. 
      apply/H2.
  - move => n0 [i_sent] P0 Q0 [j_lin] Delta HDelta H. 
    inversion H; subst => {H}.
    apply/LResP => /=. 
    inversion H2; subst => {H2}.
    + (* LParPL *) 
      inversion H3; subst => {H3} /=. 
      * (* LDelP *) 
        apply/LParPL => //. 
        move:H4 => /=.
        apply/contra_not => Hyp; right.
        apply (free_in_subst _ (scons (var_ch i_sent) ids)) => //=.
        apply/injectiveNS_scons_shift.
        move: H2. 
        simpl.
        by apply/contra_not => ->.
      * (* LDelPObj *)
        apply/LParPR => //. 
        have fact:  lin (n0.+3__ch var_zero) Q0.
        { inversion HDelta; subst. (* derive lin 0 Q0 *)
          inversion H3; subst.     (* derive lin 0 Q0 *)
          by inversion H8; subst. (* derive lin 0 Q0 *) 
        }
        apply/lin_key_subst => //.
        move:H4. 
        apply/contra_not => /= H.
        by right. 
    + (* LParPR *) 
      inversion H4; subst => {H4}. 
      apply/LParPR. 
      move:H3 => /=.
      apply/contra_not. 
      by right; right. 
      apply/lin_subst. 
      apply/H1. 
      apply/injectiveNS_scons_shift.
      move:H3 => /=.
      apply/contra_not => ->.
      by right; left. 
      by simpl.
Qed.


Lemma weakening {n : nat}: forall x T Delta (P : proc n),
    not (free_in x P) -> OFT Delta P ->	OFT (update Delta x T) P. 
Proof. 
  move => x T Delta P; elim: P x T Delta => /=.
  - move => n0 x T Delta _ _. 
    apply/TEndP.
  - move => n0 c P IH x T Delta => /Decidable.not_or; case => Hyp1 Hyp2 Hyp3.
    inversion Hyp3; subst. 
    apply/TWaitP.
    by rewrite -H1; apply/update_others.
    apply/IH => //.
  - move => n0 c P IH x T Delta => /Decidable.not_or; case => Hyp1 Hyp2 Hyp3.
    inversion Hyp3; subst. 
    apply/TCloseP.
    by rewrite -H1; apply update_others.
    apply/IH => //.
  - move => n0 P IH [i] T Delta H1 H2.
    inversion H2; subst. 
    apply/(TResP _ T0) => //.
    repeat rewrite shift_env_update. 
    apply/IH => //.
  - move => n0 P IH1 Q IH2 x T Delta H1 H2.
    inversion H2; subst. 
    move:H1 => /Decidable.not_or; case => HP HQ.
    apply/TParP.
    apply/IH1 => //.
    apply/IH2 => //.
  - move => n0 [i] P IH [j] T Delta =>/Decidable.not_or; 
            case => H1 H2 H3.
    inversion H3; subst. 
    apply/(TInSP _ _ T' T0) => //.
    rewrite/update. 
    case: ifP => /eqP => //. 
    case => H; subst => //. 
    rewrite update_swap. 
    rewrite shift_env_update.
    apply/IH => //.
    by symmetry.
  - move => n0 [i] [i0] P IH [j] T Delta =>/Decidable.not_or.
    case => H1 => /Decidable.not_or; case => H2 H3 H4. 
    inversion H4; subst. 
    apply/(TDelP _ _ _ T' (Delta (var_ch i0))) => //.
    rewrite/update. 
    case: ifP => /eqP.
    case => Hyp; subst => //.
    move => _ //.
    rewrite/update. 
    case: ifP => /eqP.
    case => Hyp; subst => //.
    move => _ //.
    rewrite update_swap.
    apply/IH => //.
    by symmetry.
Qed. 

Theorem subject_reduction : forall n P Q Delta,
    (forall x, free_in x P -> lin x P) -> 
    @reduce n P Q -> OFT Delta P -> OFT Delta Q. 
Proof.
  move => n P Q Delta Hlin H; elim: H Hlin Delta.

  (* R_Res *) 
  - move => n0 P0 Q0 Hred IH Hlin Delta H.
    inversion H; subst. 
    apply/(TResP _ T). 
    move => HZero.
    apply (lin_reduction _ P0 _ (shift_env T (shift_env (dual T) Delta))) => //.
    apply/H1. 
    by apply/(free_in_reduction _ _ Q0). 
    move => HOne. 
    apply (lin_reduction _ P0 _ (shift_env T (shift_env (dual T) Delta))) => //.
    apply/H2. 
    by apply/(free_in_reduction _ _ Q0).
    apply/IH => //.
    (* extra for extra condition below *) 
    move => [i].
    destruct i => //.
    destruct f => //.
    move:(Hlin (var_ch f)) => /= Hyp.
    move/Hyp => H'.
    inversion H'; subst. 
    apply/H5.
    
  (* R_Par *) 
  - move => n0 P0 Q0 R Hred IH Hlin Delta H. 
    inversion H; subst. 
    apply/TParP => //. 
    apply/IH => //.
    (* extra for extra condition below *) 
    move => x.
    move: (Hlin x).
    have fact : forall (X Y Z : Prop), (X \/ Y -> Z) -> X -> Z
        by move => X Y Z Hyp1 Hyp2; apply: Hyp1; left.
    move/fact.
    move => Hyp Hyp'. 
    have Hyp'' := Hyp'.
    apply Hyp in Hyp'.
    inversion Hyp';subst => //.

  (* R_Struct *)
  - move => n0 P0 P' Q0 Q' Heq1 Hred IH Heq2 Hlin Delta H. 
    apply/(subject_congruence _ Q') => //. 
    apply/IH.
    move => x Hyp.
    apply/(lin_congruence P0) => //. 
    apply/Hlin.
    apply/(free_in_congruence _ _ P') => //.
    apply/(subject_congruence _ P0) => //. 

  (* R_Close *) 
  - move => n0 P0 Q0 _ Delta H.
    inversion H; subst. 
    have fact1: lin (var_ch var_zero) (var_ch var_one ! ․ P0 ∥ var_ch var_zero ? ․ Q0) 
      by apply/H1; right; left.
    have fact2: lin (var_ch var_one) (var_ch var_one ! ․ P0 ∥ var_ch var_zero ? ․ Q0)
      by apply/H2; left; left. 
    apply/(TResP _ T). 
    + move:fact1 => /lin_free_in_wait => /=.
      by move => Hyp1 => /Hyp1.
    + move:fact2 => /lin_free_in_close => /=.
      by move => Hyp2 => /Hyp2.
    inversion H3; subst. 
    inversion H5; subst. 
    inversion H6; subst. 
    apply/TParP => //. 

    
  (* R_Del *)
  - move => n0 x P0 Q0 Hlin Delta H.
    (* 
      H = Delta ⊢ (ν) (var_one!x․P0 ∥ var_zero?(_)․Q0)
     *) 
    inversion H; subst.
    (* Inverting H, considering that TResP is invertible, we get
       HLin0 = var_zero is linear
       HLin1 = var_one is linear
       H3 = T :: (dual T) Delta ⊢ (var_one!x․P0 ∥ var_zero?(_)․Q0)
     *) 
    
    (* We now fix the linearity statememts *)
    have HLin0: lin (var_ch var_zero)
                  (var_ch var_one !x․P0 ∥ var_ch var_zero?(_)․Q0)
      by apply/H1; simpl; right; left.
    have HLin1: lin (var_ch var_one)
                  (var_ch var_one !x․P0 ∥ var_ch var_zero?(_)․Q0)
      by apply/H2; left; left. 
    move => {H1 H2}. 

    (* --------------------------------------------------------- *)
    (* Below, from linearity of zero and one, we get some facts: *)
    (* --------------------------------------------------------- *)
    have H_zero_not_in_P0: not (free_in (n0.+2__ch var_zero) P0).
    { 
      inversion HLin0; subst. 
      by move: H5 => /Decidable.not_or; case; case. 
      by move: H4; apply/contra_not => /= H'; right; right.
    }
    (**) 
    have H_x_not_one: n0.+2__ch var_one <> x.
    {
      inversion HLin1; subst. 
      by inversion H4; subst. 
      by move: H4 => /Decidable.not_or; case; case.
    }
    (**)
    have H_one_not_in_Q0_scons: not (free_in (n0.+2__ch var_one) 
                                       (subst_proc (scons x ids) Q0)).
    { 
      inversion HLin1; subst.
      move: H5; apply/contra_not => /= H'; right.
      apply/free_in_subst. 
      apply/H'.
      apply/injectiveNS_scons_shift_var_one.
      by rewrite/not => Hyp; subst. 
      by move: H4 => /Decidable.not_or; case; case. 
    }
    (**)
    have H_x_not_zero: x <> n0.+2__ch var_zero.
    {
      inversion HLin0; subst. 
      by move: H5 => /Decidable.not_or; case; case. 
      by move: H4 => /Decidable.not_or; case => _ => /Decidable.not_or; case.
    }
    (* ------------- *)
    (* End facts.    *)
    (* ------------- *)

    (* Back to the typing judgenmets, we now invert H3 *) 
    inversion H3; subst.
    (* Inverting H3, considering that TParP is invertible, we get
       H2 = T :: (dual T) Delta ⊢ var_one!x․P0
       H4 = T :: (dual T) Delta ⊢ var_zero?(_)․Q0
     *)


    (* We now invert H4, the input side *) 
    inversion H4; simpl in *; subst; simpl in *.
    rewrite update_var_zero in H7.
    (* Inverting H4, considering var_zero?()․Q0 is invertible, we get 
       (for  T = ? T0 ․ T' ) 
       H6 : lin zero Q0
       H7 :  T0 :: T' :: !T0. (dual T') :: Delta ⊢ Q0
       therefore, also updating 
       H2 : ? T0 ․ T' ::  ! T0 ․ dual T' Delta ⊢ var_one!x․P0
     *) 
    
    (* We now invert H2, the output side *) 
    inversion H2; simpl in *; subst; simpl in *.
    rewrite update_var_one in H10.
    move: H8; case => H_x_T0 Htemp2; subst. 
    (* Inverting H2, we finally get:
       H10 :        ? T0 ․ T'   ::       (dual T') :: Delta ⊢ P0
       H7  :  T0 ::        T'   ::  !T0. (dual T') :: Delta ⊢ Q0
     *) 


    apply/(TResP _ T') => /=.

    + (* Prove var_zero is linear *)
      move => _.
      inversion HLin0; subst => {HLin0 HLin1}. 
      * move:H9 => /Decidable.not_or; case; case => //.
      * inversion H9; subst. 
        apply/LParPR => //. 
        apply/(lin_subst (shift var_zero)) => //.
        apply/injectiveNS_scons_shift_var_zero => //.
    + (* Prove var_one is linear *)
      move => _.
      inversion HLin1; subst => {HLin0 HLin1}. 
      * inversion H8; subst => //. 
        apply/LParPL => //.
      * move: H8 => /= /Decidable.not_or; case; case => //. 

    + (* typability without restriction *)  
      apply/TParP.
      * have Hweak : 
          shift_env T' (shift_env (dual T') Delta) =
            update (shift_env (? T0 ․ T') (shift_env (dual T') Delta)) 
                   (var_ch var_zero) T'.
        apply/functional_extensionality => x0.
        destruct x0 => //; destruct f => //.
        rewrite Hweak.
        apply/weakening => //.
      * move:H7 => /(weakening (var_ch var_two) (dual T')) => Hyp.
        apply/substitution; last first. 
        apply/Hyp.
        move: H_one_not_in_Q0_scons.
        apply/contra_not.
        move/free_in_subst_inv. 
        apply.
        rewrite update_var_two. 
        apply/ltc_scons. 
        rewrite H_x_T0. 
        destruct x => //=.
        destruct f => //.
        destruct f => //.
        (* below, extra because of extra requirements *) 
        destruct x. 
        apply/injectiveS_scons_shift => //.
        destruct f => //.
        destruct f => //.
        move: (Hlin (var_ch f)).
        simpl.
        have fact1 : forall (X Y Z : Prop), (X \/ Y -> Z) -> X -> Z
            by move => X Y Z Hyp1 Hyp2; apply: Hyp1; left.
        have fact2 : forall (X Y Z : Prop), (X \/ Y -> Z) -> Y -> Z
            by move => X Y Z Hyp1 Hyp2; apply: Hyp1; right.
        move/fact1 => /fact2 => /fact1. 
        move => MyH.
        have fact : 
          lin (var_ch f)   
            (ResP
            (ParP 
               (DelP (var_ch var_one) (var_ch (shift (shift f))) P0)
               (InSP (var_ch var_zero) Q0))).
        apply/MyH.
        by rewrite/shift.
        inversion fact; subst. 
        inversion H5; subst. 
        move:H9 => /=.
        apply/contra_not => H11.
        by right.
        move:H8 => /=. 
        apply/contra_not => H11.
        by right; left.
Qed. 
(*
From Hammer Require Import Tactics.
Lemma weakening' {n : nat}: forall x T Delta (P : proc n),
    not (free_in x P) -> OFT Delta P ->	OFT (update Delta x T) P. 
Proof. 
intros.
generalize dependent x.
generalize dependent T.
induction H0; intros.
- sfirstorder .
- hecrush use: update_others.
Admitted.
*)