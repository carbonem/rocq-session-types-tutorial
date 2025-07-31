(* Imported libraries *) 
From mathcomp Require Import all_ssreflect.
Require Import syntax core fintype.


(* Syntax of and operations on session types *) 
Inductive sType : Type :=
| CloseT  : sType
| WaitT   : sType
| InST    : sType -> sType -> sType
| OutST   : sType -> sType -> sType
(* | OplusT  : sType -> sType -> sType *)
(* | BranchT : sType -> sType -> sType *)
.

Notation "? T  ․ U" := (InST T U) (at level 44, right associativity).
Notation "! T  ․ U" := (OutST T U) (at level 44, right associativity).

Fixpoint dual t :=
  match t with 
  | CloseT => WaitT
  | WaitT => CloseT
  | InST  s' s => OutST s' (dual s)
  | OutST s' s => InST  s' (dual s)
  (* | OplusT s1 s2 => BranchT (dual s1) (dual s2) *)
  (* | BranchT s1 s2 => OplusT (dual s1) (dual s2) *)
  end. 

Lemma dual_dual_is_identinty {S:sType} : dual (dual S) = S. 
Proof.
  elim: S => //.
  move => S' H' S H /= ; by rewrite H. 
  move => S' H' S H /= ; by rewrite H. 
Qed. 

Lemma dual_inversion {S1:sType} {S2:sType}: dual S2=S1 -> dual S1=S2.
Proof.
  by move => H; rewrite -H dual_dual_is_identinty. 
Qed. 
