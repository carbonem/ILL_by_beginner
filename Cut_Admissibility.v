(* Project files imports *)
Require Import MyLists.
Require Import Sequent_Calculus.
Require Import Basic_Properties.
Require Import Cut_One.
Require Import Cut_Atom.
Require Import Cut_Tensor.
Require Import Cut_Lolli.
Require Import Cut_With.
Require Import Cut_Oplus.

(* Other imports *)
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.


Theorem cut_admissibility : forall
    (n m : nat)
    (A C : formula)
    (Gamma Delta1 Delta2 : list formula),
    n; Gamma |- A ->
    m; (Delta1 ++ [A] ++ Delta2) |- C ->
    exists z,
       z; (Gamma ++ Delta1 ++ Delta2) |- C.
Proof.
  intros n m A.
  generalize dependent m.
  generalize dependent n.

  (* We first do induction on A *)
  (* The IH on A is used for Cut Reductions *)
  induction A.

  (* A is One -- Proven by Lemma cut_one *)
  - apply cut_one.

  (* A is Atom a -- Proven by Lemma cut_atom *)
  - intros n m.
    apply (cut_atom n m a).

  (* A is A ** B -- Proven by Lemma cut_tensor *)
  - apply (cut_tensor A1 A2 IHA1 IHA2).
    
  (* A is A -o B -- Proven by Lemma cut_lolli *)
  - apply (cut_lolli A1 A2 IHA1 IHA2).

  (* A is A # B -- Proven by Lemma cut_oplus*)
  - apply (cut_oplus A1 A2 IHA1 IHA2).

  (* A is A & B -- Proven by Lemma cut_with*)
  - apply (cut_with A1 A2 IHA1 IHA2).

Qed. 