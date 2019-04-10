(* Project files imports *)
Require Import MyLists.
Require Import Sequent_Calculus.
Require Import Basic_Properties.

(* Other imports *)
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.

Theorem cut_atom : forall
    (n m a : nat)
    (A : formula)
    (Gamma Delta1 Delta2 : list formula),
    n; Gamma |- (Atom a) 
       -> m; Delta1 ++ [Atom a] ++ Delta2 |- A
    -> exists z, z; (Gamma ++ Delta1 ++ Delta2) |- A.
Proof.
  intros n m a A Gamma Delta1 Delta2 LH.
  generalize dependent Delta2.
  generalize dependent Delta1.
  generalize dependent A.
  generalize dependent m.
  remember (Atom a) as cutformula.
  induction LH.

  (* Left premise is OneL *)
  - intros.
    specialize (IHLH Heqcutformula
                     m A0 Delta1 Delta2
                     H).
    destruct IHLH as [z Final].
    clear H. clear Heqcutformula.
    exists (S z).
    pose proof (OneL z (Gamma ++ Delta1 ++ Delta2) A0 Final).
    auto.
    

  (* Left premise is OneR *)
  - discriminate. 

  - (* Left premise is Ax *)
    intros.
    simpl in *.
    subst.
    rename H into temp.
    assert (H: m; [] ++ Delta1 ++ Atom a :: Delta2 |- A0)
      by auto.
    apply exchange_with_env_l in H.
    exists (m + length Delta1).
    apply H.
    
  - (* Left premise is TensorL *)
    intros.
    subst. 
    apply IHLH in H.
    + destruct H.
      exists (S x).
      simpl in *.
      apply (TensorL x (env ++ Delta1 ++ Delta2) A B A0).
      auto.
    + auto.
    
  - (* Left premise is TensorR *)
    discriminate.

  - (* Left premise is LolliL *)
    intros.
    subst.
    assert (eq0: Atom a = Atom a) by auto.
    apply (IHLH2 eq0) in H.
    destruct H.
    apply (level_depth n env1 A x
                       ((B :: env2) ++ Delta1 ++ Delta2) A0
                       LH1) in H.
    destruct H as [k [LH1' H]].
    exists (S k).
    simpl in *.
    rewrite <- app_assoc.
    apply (LolliL k
                  (env1) A
                  (env2 ++ Delta1 ++ Delta2) B A0
          ); assumption.

  (* Left premise is LolliR *)
  - discriminate.

  (* Left premise is WithL1 *)
  - intros m D Delta1 Delta2 RH.
    subst.
    assert (eq0: Atom a = Atom a) by auto.
    apply (IHLH eq0) in RH.
    destruct RH as [z  RH].
    simpl in *. clear eq0.

    exists (S z).
    apply WithL1; auto.

  (* Left premise is WithL2 *)
  - intros m D Delta1 Delta2 RH.
    subst.
    assert (eq0: Atom a = Atom a) by auto.
    apply (IHLH eq0) in RH.
    destruct RH as [z  RH].
    simpl in *. clear eq0.

    exists (S z).
    apply WithL2; auto.
    
  (* Left premise is WithR *)
  - discriminate.

  (* Left premise is OplusL *)
  - intros m D Delta1 Delta2 RH1.
    subst.
    assert (RH2: m; Delta1 ++ [Atom a] ++ Delta2 |- D)
      by auto.
    assert (eq0: Atom a = Atom a) by auto.
    apply (IHLH1 eq0) in RH1.
    apply (IHLH2 eq0) in RH2.
    destruct RH1 as [z  RH1].
    destruct RH2 as [z'  RH2].
    simpl in *. clear eq0.

    apply (level_depth z (A::Gamma ++ Delta1 ++ Delta2) D
                       z' (B::Gamma ++ Delta1 ++ Delta2) D
                       RH1) in RH2.
    destruct RH2 as [k [RH1' RH2']].

    exists (S k).
    apply OplusL; auto.

  (* Left premise is OplusR1 *)
  - discriminate.

  (* Left premise is OplusR1 *)
  - discriminate.

  (* Left premise is Perm *)
  - intros.
    subst.
    apply IHLH in H.
    + destruct H.
      exists (S x).
      repeat rewrite <- app_assoc.
      apply (Perm x Gamma (Delta++Delta1++Delta2) A B A0).
      repeat rewrite <- app_assoc in H.
      assumption.
    + auto.
Qed. 