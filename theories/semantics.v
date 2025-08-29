(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import syntax core fintype. 
From HB Require Import structures.

(* notations for proc here*)
(*
Open Scope subst_scope.
*)
  #[global]
  Open Scope subst_scope.
Definition var_one {n : nat} : fin (S (S n)) := shift var_zero.
Definition var_two {n : nat} : fin (S (S (S n))) := shift var_one.
Definition var_three {n : nat} : fin (S (S (S (S n)))) := shift var_two.


Notation "∅" := EndP .

Notation "0" := (var_ch var_zero) .

Notation "1" := (var_ch var_one) .

Notation "2" := (var_ch var_two) .


Notation "3" := (var_ch var_three) .
Infix "∥" := ParP (at level 48, left associativity).

Notation "(ν) p " := (ResP p) (at level 44, right associativity).
Notation "x ? (_)․ P" := (InSP x P) (at level 44, right associativity).
Notation "x ? ․ P" := (WaitP x P) (at level 44, right associativity).
Notation "x ! ․ P" := (CloseP x P) (at level 44, right associativity).
Notation "x ! y ․ P" := (DelP x y P) (at level 44, right associativity).

Notation "< sigma_ch >" := (subst_proc sigma_ch).
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

(* Decidability of equality on fin and ch *) 
Arguments var_ch {n_ch}.
Lemma fin_eq_dec {n : nat} (x y : fin n) : {x = y} + {x <> y}.
  induction n as [|m IHm] => //.
  decide equality.
Defined.
Definition ch_eq_dec {n : nat} (x y : ch n) : {x = y} + {x <> y}.
  decide equality.
  apply fin_eq_dec.
Defined.

(* Boolean equality for fin *)
Definition fin_eqb {n : nat} (x y : fin n) : bool :=
  if fin_eq_dec x y then true else false.

(* Proof that fin_eq reflects Leibniz equality *)
Lemma fin_eqP {n : nat} : Equality.axiom (@fin_eqb n).
Proof.
  move=> x y. rewrite /fin_eqb.
  destruct (fin_eq_dec x y);  now constructor.
  Qed.

HB.instance Definition _ n := hasDecEq.Build (fin n) fin_eqP.


(* Boolean equality for ch *)
Definition ch_eqb {n : nat} (x y : ch n) : bool :=
  if ch_eq_dec x y then true else false.

(* Proof that fin_eq reflects Leibniz equality *)
Lemma ch_eqP {n : nat} : Equality.axiom (@ch_eqb n).
Proof.
  move=> x y. 
  rewrite/ch_eqb.
  destruct (ch_eq_dec x y);  now constructor.
  Qed.

HB.instance Definition _ n := hasDecEq.Build (ch n) ch_eqP.


(* substitutions on processes *) 
(* am: unused
Definition shift_up {m:nat} := 
  subst_proc (fun (x:fin m) => (var_ch (shift x))).
*)
Definition shift_two_up {m:nat} := 
  subst_proc (fun (x:fin m) => (var_ch (shift(shift x)))).

Definition swap_ch {m : nat} (n1 n2 : fin m) :=
  fun n => var_ch (if n == n1 then n2 else if n == n2 then n1 else n). 




(* Structural Equivalence (or Congruence) *)
Reserved Notation "P '≅' Q" (at level 60, right associativity).
(* StartSE *)
Inductive struct_eq {n:nat} : proc n -> proc n -> Prop :=
    SC_Par_Com : forall P Q : proc n,
                 P ∥ Q ≅ Q ∥ P            
  | SC_Par_Assoc : forall P Q R : proc n,
                   P ∥ Q ∥ R ≅ P ∥ (Q ∥ R)
  | SC_Par_Inact : forall P : proc n,
                   P ∥ ∅ ≅ P
  | SC_Res_Scope : forall (P : proc n.+2) (Q : proc n),
                   (ν) P ∥ Q ≅  (ν) (P ∥ shift_two_up Q)
  | SC_Res_SwapC : forall P : proc n.+2,
                   (ν) P ≅ (ν) (< swap_ch var_zero var_one >) P                  
  | SC_Res_SwapB : forall P : proc n.+4,
                   (ν) (ν) P ≅ (ν) (ν) (< swap_ch var_one var_three >)
                     ((< swap_ch var_zero var_two >) P) 
                     (* EndSE *)
(* StartInact *)
  | SC_Res_Inact : (ν) ∅ ≅ ∅  
  (* EndInact *)                                  
  | SC_Refl : forall P : proc n, P ≅ P
  | SC_Sym : forall P Q : proc n,
             P ≅ Q -> Q ≅ P
  | SC_Trans : forall P Q R : proc n,
               P ≅ Q -> Q ≅ R -> P ≅ R
  | SC_Cong_Par : forall
                    P P' Q Q' : proc n,
                  P ≅ P' ->
                  Q ≅ Q' ->
                  P ∥ Q ≅ P' ∥ Q'
  | SC_Cong_Res : forall
                    P P' : proc n.+2,
                  P ≅ P' ->
                  (ν) P ≅ (ν) P'
  | SC_Cong_Close : forall
                      (P P' : proc n)
                      (x : ch n),
                    P ≅ P' ->
                    x ! ․ P ≅ x ! ․ P'
  | SC_Cong_Wait : forall
                     (P P' : proc n)
                     (x : ch n),
                   P ≅ P' ->
                   x ? ․ P ≅ x ? ․ P'
  | SC_Cong_OutS : forall
                     (P P' : proc n)
                     (x y : ch n),
                   P ≅ P' ->
                   x ! y ․ P
                   ≅ x ! y ․ P'
  | SC_Cong_InsP : forall
                     (P P' : proc n.+1)
                     (x : ch n),
                   P ≅ P' ->
                   x ? (_)․P
                   ≅ x ? (_)․P'
                   where   "P '≅' Q" := (struct_eq P Q).
                   

(*
  fun i => match i with
  | None => var_ch var_zero           (* 0 maps to 0 in scope n *)
  | Some None => var_ch var_zero      (* 1 also maps to 0 (they're connected) *)
  | Some (Some j) => var_ch (Some j)  (* channels 2+ shift down by 1 *)
  end.                   
Definition close_subst {n : nat} : fin n.+2 -> ch n :=
  fun i => match i with
  | None => var_ch None           (* 0 maps to 0 in the lower scope *)
  | Some None => var_ch None      (* 1 also maps to 0 (they're connected) *)
  | Some (Some j) => var_ch (j)  (* other channels shift down by 2 *)
  end.
Definition close_subst {n : nat} : fin n.+2 -> ch n :=
  fun i => match i with
  | None => var_ch n None           (* 0 maps to 0 in the lower scope *)
  | Some None => var_ch n None      (* 1 also maps to 0 (they're connected) *)
  | Some (Some j) => var_ch n (Some j)  (* other channels shift down by 2 *)
  end.

| SC_Par_Com P Q     : struct_eq (ParP P Q) (ParP Q P) 

| SC_Par_Assoc P Q R : struct_eq (ParP (ParP P Q) R) 
                         (ParP P (ParP Q R))

| SC_Par_Inact P     : struct_eq (ParP P EndP) P

| SC_Res_Scope (P : proc n.+2) (Q : proc n) : 
  struct_eq (ParP (ResP P) Q) (ResP (ParP  P (shift_two_up Q)))

| SC_Res_SwapC P : struct_eq (ResP P) 
                     (ResP (subst_proc (swap_ch var_zero var_one) P))

| SC_Res_SwapB P : struct_eq (ResP (ResP P))
                     (ResP (ResP (subst_proc (swap_ch var_one var_three)
                                    (subst_proc (swap_ch var_zero var_two) 
                                       P)))) 

(* equivalence rules *) 
| SC_Refl P          : struct_eq P P
| SC_Sym P Q         : struct_eq P Q -> struct_eq Q P
| SC_Trans P Q R     : struct_eq P Q -> struct_eq Q R -> struct_eq P R

 (* congruence rules*)
| SC_Cong_Par P P' Q Q'  : struct_eq P P' -> struct_eq Q Q' -> struct_eq (ParP P Q) (ParP P' Q')
| SC_Cong_Res P P'       : struct_eq P P' -> struct_eq (ResP P) (ResP P')
| SC_Cong_Close P P' x   : struct_eq P P' -> struct_eq (CloseP x P) (CloseP x P')
| SC_Cong_Wait P P' x    : struct_eq P P' -> struct_eq (WaitP x P) (WaitP x P')
| SC_Cong_OutS P P' x  y : struct_eq P P' -> struct_eq (DelP x y P) (DelP x y P')
| SC_Cong_InsP P P' x    : struct_eq P P' -> struct_eq (InSP x  P) (InSP x  P')
.
*)


Reserved Notation " P '⇛' Q " (at level 50, left associativity).  
      (* StartRed *)
Inductive reduce {n:nat} : proc n -> proc n -> Prop :=
  | R_Res : forall P Q : proc n.+2,
            P ⇛ Q -> (ν) P ⇛ (ν) Q
  | R_Par : forall P Q R : proc n,
            P ⇛ Q -> P ∥ R ⇛ Q ∥ R
  | R_Struct : forall P P' Q Q' : proc n,
               P ≅ P' -> P' ⇛ Q' -> Q' ≅ Q -> P ⇛ Q
  | R_Close : forall P Q : proc n.+2,
             (ν) (1 ! ․ P ∥ 0 ? ․ Q) ⇛ ((ν) (P ∥ Q)) 
  | R_Com : forall (x : ch n.+2)(P : proc n.+2) (Q : proc n.+3),
            (ν) (1 ! x ․ P ∥ 0 ? (_)․Q) ⇛ (ν) (P ∥ (< x.. >) Q) (* EndRed *)
            
where " P '⇛' Q " := (reduce P Q) . Check ids.
(*
| R_Res P Q          : reduce P Q ->
                       reduce (ResP P) (ResP Q)

| R_Par P Q R        : reduce P Q ->
                       reduce (ParP P R) (ParP Q R)

| R_Struct P P' Q Q' : struct_eq P P' ->
                       reduce P' Q' ->
                       struct_eq Q' Q ->
                       reduce P Q 

| R_Close P Q:        
  reduce (ResP (ParP (CloseP (var_ch var_one) P) 
                  (WaitP (var_ch var_zero)   Q) ))
    (ResP (ParP P Q))

| R_Del x P Q:        
  reduce (ResP (ParP (DelP (var_ch var_one) x P) 
                  (InSP (var_ch var_zero)   Q) ))
    (ResP (ParP P (subst_proc (scons x ids) Q) )) *)
    
