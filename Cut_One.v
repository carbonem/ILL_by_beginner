(* Project files imports *)
Require Import MyLists.
Require Import Sequent_Calculus.
Require Import Basic_Properties.

(* Other imports *)
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.

Theorem cut_one : forall
    (n m : nat)
    (A : formula)
    (Gamma Delta1 Delta2 : list formula),
    n; Gamma |- One
       -> m; Delta1 ++ [One] ++ Delta2 |- A
    -> exists z, z; (Gamma ++ Delta1 ++ Delta2) |- A.
Proof.
  intros n m A Gamma Delta1 Delta2 LH.
  generalize dependent Delta2.
  generalize dependent Delta1.
  generalize dependent A.
  generalize dependent m.
  remember (One) as cutformula.
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
  - clear Heqcutformula.
    intros m. 
    remember (n + m) as k.
    generalize dependent m.
    generalize dependent n.

    induction (lt_wf k) as [k _ IHl].

    intros.
    remember (Delta1 ++ [One] ++ Delta2) as context. 
    destruct H.

    (* RH is OneL *) 
    * assert (eq1: [One] ++ Gamma =
               Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq1.
      destruct eq1 as [LeftCase | RightCase].
      + destruct LeftCase as [temp1 [temp2 [l Final]]].
        clear temp1. clear temp2. 
        apply app_singleton in Final.
        destruct Final as [temp1 [temp2 Final]].
        subst.
        simpl in Heqcontext.
        inversion Heqcontext.
        subst.
        simpl in *.
        exists n0; auto.
      + destruct RightCase as [temp1 [temp2 [l Final]]].
        subst.
        assert (eq1: (One :: l) ++ [One] ++ Delta2 =
                     Delta1 ++ [One] ++ Delta2) by auto.
        apply app_inv_tail in eq1.
        subst. clear temp1. clear temp2. clear Heqcontext.
        rewrite app_assoc in H.
        apply exchange_subset in H.
        destruct H as [m [temp1 Final]].
        simpl in *.
        exists m; auto.

    (* RH is OneR *)
    * apply app_cons_not_nil in Heqcontext.
      destruct Heqcontext.

    (* RH is Axiom *)
    * apply app_singleton in Heqcontext.
      destruct Heqcontext as [temp1 [temp2 temp3]].
      subst.
      exists n.
      constructor. 

    (* RH is TensorL *)
    * assert (eq1: [A ** B] ++ env =
                   Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq1.
      destruct eq1 as [Right | Left].
      + destruct Right as [t1 [t2 [l actual]]].
        apply app_singleton in actual.
        clear t1. clear t2.
        destruct actual as [t1 [t2 t3]].
        subst.
        discriminate.
      + destruct Left as [t1 [t2 [l actual]]].
        clear t1. clear t2.
        subst.
        assert (eq1:
                   (A ** B :: l) ++ [One] ++ Delta2 =
               Delta1 ++ [One] ++ Delta2) by auto.
        apply app_inv_tail in eq1.
        subst. clear Heqcontext.
        
        assert (eq1: n + n0 < n + S n0) by omega.
        assert (eq2: n + n0 = n + n0) by omega.

        specialize (IHl (n + n0) eq1
                        n n0 eq2
                        C (A::B::l) Delta2 H).
        clear eq1. clear eq2. clear H.
        destruct IHl as [z Final].
        simpl in *.
        pose proof (TensorL z (l++Delta2) A B C Final).
        exists (S z); auto.

    (* RH is TensorR *)
    * inversion Heqcontext as [backup].
      apply element_in_app in Heqcontext. 
      destruct Heqcontext as [Left | Right].

      + destruct Left as [t1 [t2 [l sigma]]].
        subst. clear t1. clear t2.

        assert (eq: (Delta1 ++ [One]) ++ l ++ env2 =
                    (Delta1 ++ [One]) ++ Delta2)
          by (repeat rewrite <- app_assoc in *; auto).
        apply app_inv_head in eq.
        subst. clear backup.

        assert (eq1: n + n0 < n + (S n0)) by omega.
        assert (eq2: n + n0 = n + n0) by omega.

        specialize (IHl (n + n0) eq1 n n0 eq2 A Delta1 l
                        H).
        destruct IHl as [z LH].
        clear H. clear eq1. clear eq2.

        apply (level_depth z ([] ++ Delta1 ++ l) A
                           n0 env2 B LH) in H0.

        destruct H0 as [k [H1 H2]].
        simpl in *.
        exists (S k).
        pose proof (TensorR k (Delta1 ++ l) A env2 B H1 H2).
        rewrite app_assoc.
        auto.

      + destruct Right as [t1 [t2 [l Hyp]]].
        subst. clear t1. clear t2.

        assert (eq: (env1 ++ l) ++ One :: Delta2 =
                    Delta1 ++ One :: Delta2)
          by (repeat rewrite <- app_assoc in *; auto).
        apply app_inv_tail in eq.
        subst. clear backup.

        assert (eq1: n + n0 < n + (S n0)) by omega.
        assert (eq2: n + n0 = n + n0) by omega.

        specialize (IHl (n + n0) eq1 n n0 eq2 B l Delta2
                        H0).
        destruct IHl as [z LH].
        clear H0. clear eq1. clear eq2.

        apply (level_depth z ([] ++ l ++ Delta2) B
                           n0 env1 A LH) in H.

        destruct H as [k [H1 H2]].
        simpl in *.
        exists (S k).
        pose proof (TensorR k env1 A (l ++ Delta2) B H2 H1).
        rewrite <- app_assoc.
        auto.


    (* RH is LolliL *)
    * inversion Heqcontext as [backup].
      assert (eq: (A -o B :: env1) ++ env2 =
                  Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq. 
      destruct eq as [Left | Right].

      + destruct Left as [t1 [t2 [l sigma]]].
        subst. clear t1. clear t2.

        assert (eq: [A -o B] ++ env1 =
                    Delta1 ++ [One] ++ l) by auto.
        apply element_in_app in eq.
        {
          destruct eq as [LL | LR].
          
          - destruct LL as [t1 [t2 [l' single]]].
            clear t1. clear t2.
            apply app_singleton in single.
            destruct single as [t1 [t2 t3]].
            discriminate.
            
          - destruct LR as [t1 [t2 [l' single]]].
            clear t1. clear t2.
            subst.
            assert (eq: (A -o B :: l') ++ [One] ++ l =
                        Delta1 ++ [One] ++ l) by auto.
            apply app_inv_tail in eq.
            subst. 
            assert (eq: ([A -o B] ++ l' ++ [One]) ++ l ++ env2 =
                        ([A -o B] ++ l' ++ [One]) ++ Delta2)
            by (repeat rewrite <- app_assoc in *; auto).
            apply app_inv_head in eq. subst.
            clear backup. clear sigma. clear Heqcontext.

            assert (eq1: n + n0 < n + (S n0)) by omega.
            assert (eq2: n + n0 = n + n0) by omega.
            
            specialize (IHl (n + n0) eq1 n n0 eq2 A l' l
                            H).
            destruct IHl as [z LH].
            clear H. clear eq1. clear eq2.

            apply (level_depth z ([] ++ l' ++ l) A
                           n0 (B::env2) C LH) in H0.

            destruct H0 as [k [H1 H2]].
            simpl in *.
            exists (S k).
            pose proof (LolliL k (l'++l) A env2 B C H1 H2).
            rewrite <- app_assoc in H.
            auto.
        }
            
      + destruct Right as [t1 [t2 [l Hyp]]].
        subst. clear t1. clear t2.
        assert (eq: ([A -o B] ++ env1 ++ l) ++ [One] ++ Delta2 =
                    Delta1 ++ [One] ++ Delta2)
          by (repeat rewrite <- app_assoc in *; auto).
        apply app_inv_tail in eq.
        subst. clear backup. clear Heqcontext. 

        assert (eq1: n + n0 < n + (S n0)) by omega.
        assert (eq2: n + n0 = n + n0) by omega.

        specialize (IHl (n + n0) eq1 n n0 eq2 C (B::l) Delta2
                        H0).
        destruct IHl as [z LH].
        clear H0. clear eq1. clear eq2.

        apply (level_depth z ([] ++ (B::l) ++ Delta2) C
                           n0 env1 A LH) in H.

        destruct H as [k [H1 H2]].
        simpl in *.
        exists (S k).
        pose proof (LolliL k env1 A (l ++ Delta2) B C H2 H1).
        rewrite <- app_assoc.
        auto.


    (* RH is LolliR *)
    * subst.

      assert (eq1: n + n0 < n + (S n0)) by omega.
      assert (eq2: n + n0 = n + n0) by omega.
      specialize (IHl (n + n0) eq1 n n0 eq2 B (A::Delta1) Delta2
                      H).
      destruct IHl as [z H'].
      clear eq1. clear eq2. clear H.
      
      simpl in *.
      exists (S z).
      constructor; auto.

      
    (* RH is WithL1 *)
    * assert (eq: [A & B] ++  Gamma =
                  Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq.
      {
        destruct eq as [Left | Right].

        - destruct Left as [t1 [t2 [l t3]]].
          apply app_singleton in t3.
          clear t1. clear t2.
          destruct t3 as [t1 [t2 t3]].
          discriminate.

        - destruct Right as [t1 [t2 [l t3]]].
          subst. clear t1. clear t2.
          assert (eq: (A & B :: l) ++ ([One] ++ Delta2) =
                      Delta1 ++ ([One] ++ Delta2))
            by auto.
          apply app_inv_tail in eq.
          subst. clear Heqcontext.

          assert (eq1: n + n0 < n + (S n0)) by omega.
          assert (eq2: n + n0 = n + n0) by omega.
          assert (eq3: n0; (A :: l) ++ [One] ++ Delta2 |- C)
            by auto.
          specialize (IHl (n + n0) eq1 n n0 eq2
                          C (A::l) Delta2
                      eq3).
          destruct IHl as [z H'].
          clear eq1. clear eq2. clear H. clear eq3.

          simpl in *.
          exists (S z).
          apply WithL1; auto.
      }
      
      
    (* RH is WithL2 *)
    * assert (eq: [A & B] ++  Gamma =
                  Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq.
      {
        destruct eq as [Left | Right].

        - destruct Left as [t1 [t2 [l t3]]].
          apply app_singleton in t3.
          clear t1. clear t2.
          destruct t3 as [t1 [t2 t3]].
          discriminate.

        - destruct Right as [t1 [t2 [l t3]]].
          subst. clear t1. clear t2.
          assert (eq: (A & B :: l) ++ ([One] ++ Delta2) =
                      Delta1 ++ ([One] ++ Delta2))
            by auto.
          apply app_inv_tail in eq.
          subst. clear Heqcontext.

          assert (eq1: n + n0 < n + (S n0)) by omega.
          assert (eq2: n + n0 = n + n0) by omega.
          assert (eq3: n0; (B :: l) ++ [One] ++ Delta2 |- C)
            by auto.
          specialize (IHl (n + n0) eq1 n n0 eq2
                          C (B::l) Delta2
                      eq3).
          destruct IHl as [z H'].
          clear eq1. clear eq2. clear H. clear eq3.

          simpl in *.
          exists (S z).
          apply WithL2; auto.
      }

      
    (* RH is WithR *)
    * subst. 
      assert (eq1: n + n0 < n + (S n0)) by omega.
      assert (eq2: n + n0 = n + n0) by omega.
      assert (IHl': forall y : nat,
                 y < n + S n0 ->
                 forall n m : nat,
                   y = n + m ->
                   forall (A : formula)
          (Delta1 Delta2 : list formula),
        m; Delta1 ++ [One] ++ Delta2 |- A ->
        exists z : nat,
          z; [] ++ Delta1 ++ Delta2 |- A) by auto.
      specialize (IHl (n + n0) eq1 n n0 eq2
                      A Delta1 Delta2
                      H).
      clear H.
      destruct IHl as [z H].
      specialize (IHl' (n + n0) eq1 n n0 eq2
                      B Delta1 Delta2
                      H0).
      destruct IHl' as [z' H'].
      clear eq1. clear eq2. clear H0.

      apply (level_depth z (Delta1 ++ Delta2) A
                         z' (Delta1 ++ Delta2) B
                         H) in H'.
      destruct H' as [k [H1 H2]].
      exists (S k).
      apply WithR; auto.

    (* RH is OplusL *)
    * subst.
      assert (eq: [A # B] ++ Gamma =
                  Delta1 ++ [One] ++ Delta2) by auto.
      apply element_in_app in eq.
      {
        destruct eq as [Left | Right].

        - destruct Left as [t1 [t2 [l t3]]].
          clear t1. clear t2.
          apply app_singleton in t3.
          destruct t3 as [t1 [t2 t3]].
          discriminate.

        - destruct Right as [t1 [t2 [l t3]]].
          subst. clear t1. clear t2.
          assert (eq: (A # B :: l) ++ ([One] ++ Delta2) =
                      Delta1 ++ ([One] ++ Delta2)) by auto.
          apply app_inv_tail in eq.
          subst. clear Heqcontext.

          assert (eq1: n + n0 < n + (S n0)) by omega.
          assert (eq2: n + n0 = n + n0) by omega.
          assert (IHl': forall y : nat,
                     y < n + S n0 ->
                     forall n m : nat,
                       y = n + m ->
                       forall (A : formula)
                              (Delta1 Delta2 : list formula),
                         m; Delta1 ++ [One] ++ Delta2 |- A ->
        exists z : nat,
          z; [] ++ Delta1 ++ Delta2 |- A) by auto.
          specialize (IHl (n + n0) eq1 n n0 eq2
                          C (A::l) Delta2
                          H).
          clear H.
          destruct IHl as [z H].
          specialize (IHl' (n + n0) eq1 n n0 eq2
                           C (B::l) Delta2
                           H0).
          destruct IHl' as [z' H'].
          clear eq1. clear eq2. clear H0.
          
          apply (level_depth z ((A::l) ++ Delta2) C
                             z' ((B::l) ++ Delta2) C
                             H) in H'.
          destruct H' as [k [H1 H2]].
          exists (S k).
          apply OplusL; auto.
      }


    (* RH is OplusR1 *)
    * subst.
      assert (eq1: n + n0 < n + (S n0)) by omega.
      assert (eq2: n + n0 = n + n0) by omega.
      specialize (IHl (n + n0) eq1 n n0 eq2
                      A Delta1 Delta2 H).
          destruct IHl as [z H'].
          clear eq1. clear eq2. clear H. 

          simpl in *.
          exists (S z).
          apply OplusR1; auto.


    (* RH is OplusR2 *)
    * subst.
      assert (eq1: n + n0 < n + (S n0)) by omega.
      assert (eq2: n + n0 = n + n0) by omega.
      specialize (IHl (n + n0) eq1 n n0 eq2
                      B Delta1 Delta2 H).
          destruct IHl as [z H'].
          clear eq1. clear eq2. clear H. 

          simpl in *.
          exists (S z).
          apply OplusR2; auto.

    (* RH is Perm *)
    * inversion Heqcontext as [backup].
      apply elements_in_app in backup.
      {
        destruct backup as [First | Remaining].

        - destruct First as [t1 [l t2]].
          subst. clear t1.
          assert (eq: (Delta1 ++ [One])
                    ++ l ++ [B] ++ [A] ++ Delta =
                  (Delta1 ++ [One]) ++ Delta2)
            by (repeat rewrite <- app_assoc in *; auto ).
          apply app_inv_head in eq.
          subst. clear Heqcontext.

          repeat rewrite <- app_assoc in *.
          assert (eq1: n + n0 < n + (S n0)) by omega.
          assert (eq2: n + n0 = n + n0) by omega.
          specialize (IHl (n + n0) eq1 n n0 eq2 C
                          Delta1 (l ++ [A] ++ [B] ++ Delta) H).
          destruct IHl as [z H'].
          clear eq1. clear eq2. clear H.

          simpl in *.
          rewrite app_assoc in *.
          exists (S z).
          constructor; auto.

        - destruct Remaining as [Next | Remaining].

          * destruct Next as [t1 [t2 t3]].
            subst. clear Heqcontext.

            rewrite app_assoc in H.
            assert (eq1: n + n0 < n + (S n0)) by omega.
            assert (eq2: n + n0 = n + n0) by omega.
            specialize (IHl (n + n0) eq1 n n0 eq2 C
                            (Delta1++[A]) Delta H).
            destruct IHl as [z H'].
            clear eq1. clear eq2. clear H.
            
            exists z.
            simpl in *.
            rewrite <- app_assoc in H'; auto.

          * destruct Remaining as [Next | Last].

            + destruct Next as [t1 [t2 t3]].
              subst. clear Heqcontext.
              assert (eq1: n + n0 < n + (S n0)) by omega.
              assert (eq2: n + n0 = n + n0) by omega.
              specialize (IHl (n + n0) eq1 n n0 eq2 C
                              Gamma ([B] ++ Delta2) H).
              destruct IHl as [z H'].
              clear eq1. clear eq2. clear H.

              exists z.
              simpl in *.
              rewrite <- app_assoc; auto.

            + destruct Last as [t1 [l t2]].
              subst. clear t1.
              assert (eq: (Gamma ++ [B] ++ [A] ++ l) ++
                                [One] ++ Delta2 =
                          Delta1 ++ [One] ++ Delta2)
                by (repeat rewrite <- app_assoc in *; auto).
              apply app_inv_tail in eq.
              subst. clear Heqcontext.

              rewrite app_assoc in H.
              rewrite app_assoc in H.
              rewrite app_assoc in H.
              assert (eq1: n + n0 < n + (S n0)) by omega.
              assert (eq2: n + n0 = n + n0) by omega.
              specialize (IHl (n + n0) eq1 n n0 eq2 C
                              (((Gamma ++ [A]) ++ [B]) ++ l)
                              Delta2 H).
              destruct IHl as [z H'].
              clear eq1. clear eq2. clear H.
              
              exists (S z).
              repeat rewrite <- app_assoc in *.
              constructor.
              auto.
      }
          
  - (* Left premise is Ax *)
    intros.
    simpl in *.
    subst.
    rename H into temp.
    assert (H: m; [] ++ Delta1 ++ One :: Delta2 |- A0)
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
    assert (eq0: One = One) by auto.
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

  - (* Left premise is LolliR *)
    discriminate.

  - (* Left premise is WithL1 *)
    intros.
    subst.
    assert (eq0: One = One) by auto.
    apply (IHLH eq0) in H.
    clear eq0.
    
    destruct H as [z H].
    simpl in *.
    exists (S z).
    apply WithL1; auto.
    
  - (* Left premise is WithL2 *)
    intros.
    subst.
    assert (eq0: One = One) by auto.
    apply (IHLH eq0) in H.
    clear eq0.
    
    destruct H as [z H].
    simpl in *.
    exists (S z).
    apply WithL2; auto.
    
  - (* Left premise is WithR *)
    discriminate.
    
  - (* Left premise is OplusL *)
    intros.
    subst.

    assert (H': m; Delta1 ++ [One] ++ Delta2 |- A0) by auto.
    
    assert (eq0: One = One) by auto.
    apply (IHLH1 eq0) in H.
    clear eq0. 

    assert (eq0: One = One) by auto.
    apply (IHLH2 eq0) in H'.
    clear eq0.

    destruct H as [z H].
    destruct H' as [z' H'].
    simpl in *.

    apply (level_depth z  (A:: Gamma ++ Delta1 ++ Delta2) A0
                       z' (B:: Gamma ++ Delta1 ++ Delta2) A0
                       H) in H'.
    destruct H' as [k [ H1 H2]].
    exists (S k).
    apply OplusL; auto.

  - (* Left premise is OplusR1 *)
    discriminate.

  - (* Left premise is OplusR2 *)
    discriminate.

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