From mathcomp Require Import all_ssreflect.

From HB Require Import structures.


Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.


Inductive ch (n_ch : nat) : Type :=
    var_ch : fin n_ch -> ch n_ch.


Arguments var_ch {n_ch}.
Lemma fin_eq_dec {n : nat} (x y : fin n) : {x = y} + {x <> y}.
  induction n as [|m IHm] => //.
  decide equality.
Defined.
Definition ch_eq_dec {n : nat} (x y : ch n) : {x = y} + {x <> y}.
  decide equality.
  apply fin_eq_dec.
Defined.


Definition swap_ch {m_ch : nat} (n1 n2 : fin m_ch) : fin m_ch -> ch m_ch :=
  fun n => var_ch (if is_left (fin_eq_dec n n1)
   then n2
   else
    if is_left (fin_eq_dec n n2)
    then n1
    else n).


(* new stuff *)

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


(* Now you can use your swap_ch' definition *)
Definition swap_ch' {m_ch : nat} (n1 n2 : fin m_ch) :=
  fun n => var_ch (if n == n1 then n2 else if n == n2 then n1 else n). 
  