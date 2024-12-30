(* Necessary imports *)
Require Import Coq.Init.Nat.
Require Import Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.


Class EuclidianGeometry (Point : Type) := {

  (* Core relations that define geometric relationships *)

  is_collinear : Point -> Point -> Point -> Prop;     (* Three points lie on a line *)
  is_between : Point -> Point -> Point -> Prop;       (* Second point lies between first and third *)

  (* Axiom: If points A,B,C are collinear, then C,B,A are also collinear *)
  collinear_symmetric : forall A B C : Point,
    is_collinear A B C -> is_collinear C B A;
    
  (* Axiom: If points A,B,C are collinear, then A,C,B are also collinear *)
  collinear_swap_23 : forall A B C : Point,
    is_collinear A B C -> is_collinear A C B;

  (* Axiom: No point can be between itself and another point *)
  between_irreflexive12 : forall P Q : Point, 
    ~ is_between P P Q;

  (* Axiom: If B is between A and C, then B is between C and A *)
  between_symmetric : forall A B C : Point, 
    is_between A B C -> is_between C B A
}.

Section GeometryTheorems.

(*
`Context` declares that we'll be using an instance `G` of the `Geometry` type class with type parameters `Point`. 
This makes the type class's fields and axioms available in all theorems below.
*)

Context {Point : Type} {G : EuclidianGeometry Point}.

(* Theorem: If A,B,C are collinear, then C,A,B are collinear *)
Theorem collinear_rotate :
  forall A B C : Point,
  is_collinear A B C -> is_collinear C A B.
Proof.
  intros A B C H.
  apply collinear_symmetric in H.
  apply collinear_swap_23 in H.
  exact H.
Qed.

(* Theorem: If A,B,C are collinear, then B,A,C are collinear *)
Theorem collinear_swap12 :
  forall A B C : Point,
  is_collinear A B C -> is_collinear B A C.
Proof.
  intros A B C H.
  apply collinear_rotate in H.
  apply collinear_symmetric in H.
  exact H.
Qed.

(* Theorem: A point cannot be between a point and itself *)
Theorem between_irreflexive23 :
  forall P Q : Point, ~ is_between P Q Q.
Proof.
(*  
  intros P Q H1.
  apply between_symmetric in H1.
  apply between_irreflexive12 in H1.
  contradiction.
*)  
  admit.
Admitted.

(* Theorem: If Q is between P and R, then Q is distinct from both P and R *)
Theorem between_points_distinct :
  forall P Q R : Point,
    is_between P Q R -> Q <> P /\ Q <> R.
Proof.
  intros P Q R H.
  split.
  - intro H1.
    rewrite H1 in H.
    apply between_irreflexive12 in H.
    contradiction.
  - intro H2.
    rewrite H2 in H.
    apply between_symmetric in H.
    apply between_irreflexive12 in H.
    contradiction.
Qed.

End GeometryTheorems.

Section EuclidianGeometryInstance.

Theorem nat_collinear_symmetric : forall A B C : nat,
  True -> True.
Proof.
  intros A B C H.
  exact I.
Qed.

Theorem nat_collinear_swap_23 : forall A B C : nat,
  True -> True.
Proof.
  intros A B C H.
  exact I.
Qed.


Theorem nat_between_irreflexive12 : forall P Q : nat,
  ~ ((P < P < Q) \/ (Q < P < P)).
Proof.
  (* Let P and Q be arbitrary natural numbers *)
  intros P Q.
  
  (* We want to prove the negation of the disjunction *)
  unfold not.
  intros H.
  
  (* Case analysis on the disjunction *)
  destruct H as [H1 | H2].
  
  (* Case 1: P < P < Q *)
  - destruct H1 as [H11 H12].
    (* P < P is impossible for natural numbers *)
    apply (Nat.lt_irrefl P H11).
    
  (* Case 2: Q < P < P *)
  - destruct H2 as [H21 H22].
    (* P < P is impossible for natural numbers *)
    apply (Nat.lt_irrefl P H22).
Qed.


Theorem nat_between_symmetric : forall A B C : nat,
  ((A < B < C) \/ (C < B < A)) -> ((C < B < A) \/ (A < B < C)).
Proof.
  (* Let A, B, C be arbitrary natural numbers *)
  intros A B C.
  
  (* Let H be our hypothesis that B is between A and C *)
  intros H.
  
  (* Destruct the disjunction in our hypothesis *)
  destruct H as [H1 | H2].
  
  (* Case 1: A < B < C *)
  - destruct H1 as [H11 H12].
    (* We need to prove (C < B < A) \/ (A < B < C) *)
    (* We can use the right disjunct *)
    right.
    split; assumption.
    
  (* Case 2: C < B < A *)
  - destruct H2 as [H21 H22].
    (* We need to prove (C < B < A) \/ (A < B < C) *)
    (* We can use the left disjunct *)
    left.
    split; assumption.
Qed.

(* Instance of EuclidianGeometry using nat as Point *)
#[local] Instance EuclidianGeometryN : EuclidianGeometry(nat) := {

  (* All points are collinear *)
  is_collinear := fun A B C => True;
  
  (* Betweeness is defined based on ordering *)
  is_between := fun A B C => (A < B < C) \/ (C < B < A);  

  (* Axioms *)

  collinear_symmetric := nat_collinear_symmetric;
  collinear_swap_23 := nat_collinear_swap_23;
  
  between_irreflexive12 := nat_between_irreflexive12;
  between_symmetric := nat_between_symmetric;
}.

End EuclidianGeometryInstance.
