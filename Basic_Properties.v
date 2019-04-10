(* Project files imports *)
Require Import Sequent_Calculus.
Require Import MyLists.

(* Other imports *)
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.


(* This file contains basic lemmas about |- *)

Lemma incr_succ : forall n Gamma A,
    mill n Gamma A -> mill (S n) Gamma A.
Proof.
  intros. 
  induction H.
  - apply (OneL (S n) Gamma A); auto.
  - apply OneR.
  - apply (Ax (S n) A).
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.


Lemma incr_m : forall (n m : nat) Gamma A,
    mill n Gamma A -> mill (n + m) Gamma A.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros.
    rewrite Nat.add_0_r; auto.

  - intros.
    apply IHm in H.
    apply incr_succ in H.
    rewrite Nat.add_succ_r; auto.
Qed. 
    

Lemma level_depth: forall n Gamma A m Delta B,
    (n; Gamma |- A) -> (m; Delta |- B)
    -> exists k, (k; Gamma |- A) /\ (k; Delta |- B).
Proof.
  intros. 
  assert (either : n >= m \/ m >= n) by omega.
  destruct either.
  * apply (incr_m m (n-m)) in H0.
    assert (m + (n-m) = n) by omega.
    rewrite H2 in H0.
    exists n. split; auto.
  * apply (incr_m n (m-n)) in H.
    assert (n + (m-n) = m) by omega.
    rewrite H2 in H.
    exists m. split; auto.
Qed. 


Lemma ax_0 : forall Gamma A,
    0; Gamma |- A -> Gamma = [A] \/ Gamma = [].
Proof. 
  intros.
  inversion H; auto.
Qed.


Lemma exchange_with_env_l:
  forall (n: nat)
         (Gamma env Delta : list formula)
         (A B : formula),
    ( n ; (Gamma ++ env ++ [A] ++ Delta) |- B )
    ->
    ((n + length env); (Gamma ++
                              [A] ++ env
                              ++ Delta ) |- B).
Proof.
  intros n Gamma env.
  generalize dependent Gamma.
  generalize dependent n.
  induction env.

  - intros.
    simpl in *.
    rewrite Nat.add_0_r.
    auto.

  - intros.
    assert ( 
        n; Gamma ++ [a] ++ env ++ [A] ++ Delta |- B)
      by auto.
    rewrite app_assoc in H0.

    specialize (IHenv n
                      (Gamma ++ [a])
                      Delta
                      A B H0).

    rewrite <- app_assoc in IHenv.

    assert (num : n + S (length env) = S (n + length env))
      by omega.

    pose proof (Perm (n + length env)
                     Gamma
                     (env ++ Delta)
                     a A B IHenv).

    simpl in *.
    rewrite Nat.add_succ_r.
    auto.
Qed.


Lemma exchange_with_env_r :
  forall (n: nat)
         (Gamma env Delta : list formula)
         (A B : formula),
    (n ; (Gamma ++ [A] ++ env ++ Delta) |- B )
    ->
    (n + length env) ; (Gamma ++ env ++ [A] ++ Delta) |- B.
Proof.
  intros n Gamma env.
  generalize dependent Gamma.
  generalize dependent n.
  induction env.

  - intros.
    simpl in *.
    rewrite Nat.add_0_r.
    auto.

  - intros.
    assert ( 
        n; Gamma ++ [A] ++ [a] ++ env ++ Delta |- B)
      by auto.

    pose proof (Perm n
                     Gamma
                     (env ++ Delta)
                     A
                     a
                     B
                     H0).
    
    assert ( Hyp: 
               S n; (Gamma ++ [a]) ++ [A] ++ env ++ Delta
                    |- B
           )
      by (rewrite <- app_assoc; auto).

    specialize (IHenv (S n)
                      (Gamma ++ [a])
                      Delta
                      A B Hyp).

    rewrite <- app_assoc in IHenv.

    assert (num : n + S (length env) = S (n + length env))
      by omega.
    simpl in *.
    rewrite Nat.add_succ_r.
    auto.
Qed.

    
Lemma exchange_subset :
  forall (n: nat)
         (Gamma1 Gamma2 Delta : list formula)
         (A : formula),
    mill n ((Gamma1 ++ Gamma2) ++ Delta) A ->
    exists m, m >=n /\
              mill m ((Gamma2 ++ Gamma1) ++ Delta) A.
Proof.
  intros n Gamma1 Gamma2.
  generalize dependent Gamma1.
  generalize dependent n.
  induction Gamma2.
  - intros.
    simpl in *.
    rewrite app_nil_r in H.
    exists n.
    split; auto.

  - intros.
    assert (n; (Gamma1 ++ [a] ++ Gamma2) ++ Delta |- A)
           by auto.
    repeat rewrite <- app_assoc in H0.
    rename H0 into temp.
    assert (H0: n; [] ++
                      Gamma1 ++ [a] ++
                      Gamma2 ++ Delta |- A)
      by auto.
    apply exchange_with_env_l in H0.
    rename H0 into temp2.
    assert (H0 :
              (n + Datatypes.length Gamma1);
            [a] ++ Gamma1 ++ Gamma2 ++ Delta
            |- A) by auto.
    rewrite app_assoc in H0.
    rewrite app_assoc in H0.
    remember (n + Datatypes.length Gamma1) as x. 
    specialize (IHGamma2 x ([a] ++ Gamma1) Delta A H0).
    destruct IHGamma2.
    destruct H1.
    rewrite <- app_assoc in *.
    assert ( x0; Gamma2 ++ ([a] ++ Gamma1) ++ Delta
                 |- A) by auto.
    rewrite <- app_assoc in *.
    assert (H4: x0; [] ++
                       Gamma2 ++ [a] ++
                       Gamma1 ++ Delta
                          |- A)
      by auto.
    apply exchange_with_env_l in H4.
    exists (x0 + length Gamma2).
    split.
    + omega.
    + assert ((x0 + length Gamma2);
              [a] ++ Gamma2 ++ Gamma1 ++ Delta |- A)
        by auto.
      rewrite app_assoc in H5.
      auto.
Qed. 
